/-
Copyright (c) 2024. All rights reserved.

# Exclusion of the class-three configuration `P² = P'` and `(P')² = Z(P)`

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96.

`Work.Higman.LayersAlt.class_three_exclusion`: a Suzuki 2-group `P` with a fixed-point-free
automorphism `ξ` of order `|Z(P)| - 1` (`FpfXi ξ`) cannot satisfy simultaneously

* `P² = P'` (`hP2`),   and
* `(P')² = Z(P)` (`hsq2`).

This is the "class three" branch of the reduction of
`Work.Higman.LayersAlt.sq_mem_center_fpf` (every square of `P` is central): if the derived
subgroup `P'` is not contained in the centre then `P = P' = P²` describes the `C₄` shape of
`P'`, and Higman's Lemma 8 forbids it.

## The proof

Write `D = P'` and `Z = Z(P)`.

1. `Z = Ω₁(P)` (`center_eq_omega1_of_fpf`), and `Z = D² ≤ D` (`hsq2`).
2. `D` is `ξ`-invariant (it is characteristic), so the `⟨ξ⟩`-orbits on `D ∖ {1}` have
   `orderOf ξ = |Z| - 1` elements; since `|D|` is a power of `2` and `|D| ∣ |P| = |Z|³`, the
   divisibility `|Z| - 1 ∣ |D| - 1` forces `|D| ∈ {|Z|, |Z|², |Z|³}`
   (`card_derivTop_trichotomy`).
3. `|D| = |Z|` gives `D = Z`, whence `(D)² = D` by `hsq2`; but `Z = Ω₁(P)` has exponent `2`,
   so `Z = 1`, contradicting `4 ≤ |Ω₁(P)|`.
4. `|D| = |Z|³` gives `D = P`, contradicting `derivTop_ne_top` (a nontrivial finite `2`-group
   is not perfect).
5. So `|D| = |Z|²`.  Higman's Lemma 9 (`higman9_exists_new`) provides a maximal `ξ`-invariant
   abelian normal subgroup `A ⊇ P'`, so `D` is abelian.
   Consider `C = ⊤ ⊇ D`.  Every `ξ`-invariant `E` with `D ≤ E` has order `|D| = |Z|²` or
   `|P| = |Z|³` (`eq_or_top_of_le_of_card_sq_aux` below, again an orbit count), so the pair
   `(A, C) = (D, ⊤)` satisfies the covering hypothesis of Higman's Lemma 8, which we invoke in
   its axiom-clean form `Work.Higman.MSA.lemma8_clean` for the automorphism `ξ` (legitimate
   because `ξ` is itself transitive on the involutions, `isSuzuki2Grp_of_fpfXi`).
   Lemma 8 gives `a * a = 1` for every `a ∈ D`, i.e. `D² = 1`; with `Z = D²` this contradicts
   `4 ≤ |Ω₁(P)|`.

The order dichotomy of step 5 is proved below as `eq_or_top_of_le_of_card_sq_aux`; the same
statement was also delegated as `Work.Higman.LayersAlt.eq_or_top_of_le_of_card_sq` (a separate
module, not imported here).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.LayersAlt.fpf_defs
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.BS.fpf
import Submission.Work.Higman.HS.core_mul
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.LayersAlt.isSuzuki2Grp_of_fpfXi
import Submission.Work.Higman.LayersAlt.card_derivTop_trichotomy
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.higman9_exists_new
import Submission.Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.LayersAlt

/-- **Auxiliary: an order dichotomy.**  Let `A ≤ E` be subgroups of a Suzuki 2-group `P`, with
`E` invariant under the fixed-point-free automorphism `ξ` and `|A| = |Z(P)|²`.  Then `E = A` or
`E = ⊤`.

Indeed `⟨ξ⟩` acts on `E ∖ {1}` with all `|Z(P)| - 1` elements (fixed-point-freeness), so
`|Z(P)| - 1 ∣ |E| - 1`; with `|E| = |A| · [E : A] = |Z(P)|² · d` and `1 ≤ d ≤ |Z(P)|` this forces
`d = 1` (whence `E = A`) or `d = |Z(P)|` (whence `|E| = |P|` and `E = ⊤`). -/
theorem eq_or_top_of_le_of_card_sq_aux {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) {A E : Subgroup P} (hAE : A ≤ E)
    (hEinv : E.map ξ.toMonoidHom = E)
    (hcardA : Nat.card ↥A = Nat.card ↥(Subgroup.center P) ^ 2) :
    E = A ∨ E = ⊤ := by
  classical
  -- `Z(P) = Ω₁(P)` has at least `4` elements
  have hZom : Subgroup.center P = Work.Higman.omega1 P := center_eq_omega1_of_fpf h hξ
  have hq4 : 4 ≤ Nat.card ↥(Subgroup.center P) := by
    rw [hZom]; exact h.omega1_card_ge_four
  -- the orbit count: `|Z| - 1 ∣ |E| - 1`
  have hdvd : (Nat.card ↥(Subgroup.center P) - 1) ∣ (Nat.card ↥E - 1) :=
    Work.Higman.Layers.card_dvd_card_sub_one_of_map_xi_eq h hξ hEinv
  -- `|E| = |A| * [E : A]`
  have hcardE : Nat.card ↥E = Nat.card ↥A * A.relIndex E := by
    have h1 : Nat.card ↥(A.subgroupOf E) * (A.subgroupOf E).index = Nat.card ↥E :=
      (A.subgroupOf E).card_mul_index
    have h2 : Nat.card ↥(A.subgroupOf E) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE)
    rw [h2] at h1
    exact h1.symm
  -- `|A| ≤ |E| ≤ |P|`
  have hAle : Nat.card ↥A ≤ Nat.card ↥E :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hAE) (Subgroup.inclusion_injective hAE)
  have hEle : Nat.card ↥E ≤ Nat.card P := Subgroup.card_le_card_group E
  have hPcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := hξ.card_cube
  -- `1 ≤ d` and `d ≤ |Z|`, where `d = A.relIndex E`
  have hd1 : 1 ≤ A.relIndex E := by
    have h1 : Nat.card ↥A * 1 ≤ Nat.card ↥A * A.relIndex E := by
      rw [mul_one, ← hcardE]; exact hAle
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  have hdle : A.relIndex E ≤ Nat.card ↥(Subgroup.center P) := by
    have h1 : Nat.card ↥A * A.relIndex E ≤ Nat.card ↥A * Nat.card ↥(Subgroup.center P) := by
      rw [← hcardE, hcardA]
      calc Nat.card ↥E ≤ Nat.card P := hEle
        _ = Nat.card ↥(Subgroup.center P) ^ 2 * Nat.card ↥(Subgroup.center P) := by
            rw [hPcard, pow_succ]
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  -- the arithmetic: `1 ≡ d [MOD |Z| - 1]`, whence `|Z| - 1 ∣ d - 1`
  have hmod : 1 ≡ A.relIndex E [MOD (Nat.card ↥(Subgroup.center P) - 1)] := by
    set q := Nat.card ↥(Subgroup.center P) with hqdef
    have hq0 : 0 < q := by rw [hqdef]; omega
    have hq1 : q ≡ 1 [MOD (q - 1)] :=
      ((Nat.modEq_iff_dvd' (a := 1) (b := q) (n := q - 1) (by omega)).mpr dvd_rfl).symm
    have hmult : q ^ 2 * A.relIndex E ≡ A.relIndex E [MOD (q - 1)] := by
      simpa using (hq1.pow 2).mul (Nat.ModEq.refl (A.relIndex E))
    have hqd : q ^ 2 * A.relIndex E ≡ 1 [MOD (q - 1)] := by
      have h' : (q - 1) ∣ q ^ 2 * A.relIndex E - 1 := by
        rw [hcardE, hcardA] at hdvd
        exact hdvd
      refine ((Nat.modEq_iff_dvd' (a := 1) (b := q ^ 2 * A.relIndex E) (n := q - 1) ?_).mpr
        h').symm
      have hh : 0 < q ^ 2 * A.relIndex E := Nat.mul_pos (pow_pos hq0 2) (by omega)
      omega
    exact hqd.symm.trans hmult
  have hdvdd : (Nat.card ↥(Subgroup.center P) - 1) ∣ (A.relIndex E - 1) :=
    (Nat.modEq_iff_dvd' hd1).mp hmod
  -- conclude
  rcases Nat.eq_zero_or_pos (A.relIndex E - 1) with h0 | hpos
  · left
    have hd : A.relIndex E = 1 := by omega
    have h1 : Nat.card ↥E = Nat.card ↥A := by rw [hcardE, hd, mul_one]
    exact (Subgroup.eq_of_le_of_card_ge hAE (le_of_eq h1)).symm
  · right
    have hle' : Nat.card ↥(Subgroup.center P) - 1 ≤ A.relIndex E - 1 :=
      Nat.le_of_dvd hpos hdvdd
    have hle'' : A.relIndex E - 1 ≤ Nat.card ↥(Subgroup.center P) - 1 := by omega
    have hd : A.relIndex E = Nat.card ↥(Subgroup.center P) := by omega
    have h1 : Nat.card ↥E = Nat.card P := by
      rw [hcardE, hd, hcardA, hPcard, ← pow_succ]
    exact Subgroup.eq_top_of_card_eq E h1

theorem class_three_exclusion {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hP2 : Work.Higman.LayersAlt.sqSub P = Work.Higman.LayersAlt.derivTop P)
    (hsq2 : Work.Higman.powSub (Work.Higman.LayersAlt.derivTop P) 2 = Subgroup.center P) :
    False := by
  classical
  haveI : Nontrivial P := h.nontrivial
  -- `Z(P) = Ω₁(P)`
  have hZom : Subgroup.center P = Work.Higman.omega1 P := center_eq_omega1_of_fpf h hξ
  -- `Z(P) ≤ P'`, since `Z(P) = (P')^(2)`
  have hZD : Subgroup.center P ≤ derivTop P := by
    rw [← hsq2]
    exact Work.Higman.powSub_le (A := derivTop P) (n := 2) (by norm_num)
  -- the order of `P'` is `|Z|`, `|Z|²` or `|Z|³`
  rcases card_derivTop_trichotomy h hξ with hc | hc | hc
  · -- ## `|P'| = |Z|`: then `P' = Z(P) = Ω₁(P)`
    have hDZ : Subgroup.center P = derivTop P :=
      Subgroup.eq_of_le_of_card_ge hZD (le_of_eq hc)
    have hpow : Work.Higman.powSub (Subgroup.center P) 2 = Subgroup.center P := by
      rw [hDZ, hsq2, hDZ]
    -- every element of `Z(P) = Ω₁(P)` is an involution, so `Z(P)² = 1`
    have hZ2bot : Work.Higman.powSub (Subgroup.center P) 2 ≤ ⊥ := by
      rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      rw [hZom] at hx
      exact Subgroup.mem_bot.mpr (by simpa [pow_two] using h.mem_omega1.mp hx)
    have hZbot : Subgroup.center P = ⊥ := le_bot_iff.mp (hpow ▸ hZ2bot)
    have hcard1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
      rw [← hZom, hZbot]
      simp
    have h4 := h.omega1_card_ge_four
    omega
  · -- ## `|P'| = |Z|²`: the `C₄` configuration, excluded by Higman's Lemma 8
    -- `P'` is abelian: it lies in a maximal `ξ`-invariant abelian normal subgroup
    obtain ⟨A, hAis, -, -, hDA, -, -⟩ := Work.Higman.higman9_exists_new h
    have hDab : ∀ x ∈ derivTop P, ∀ y ∈ derivTop P, x * y = y * x :=
      fun x hx y hy => hAis.abelian x (hDA hx) y (hDA hy)
    -- `ξ` itself is a Suzuki-automorphism, so Lemma 8 may be used with `ξ`
    obtain ⟨h', h'xi⟩ := isSuzuki2Grp_of_fpfXi h hξ
    have hexpD : ∀ a ∈ derivTop P, a * a = 1 :=
      Work.Higman.MSA.lemma8_clean h' (A := derivTop P) (C := ⊤)
        ⟨Subgroup.commutator_normal ⊤ ⊤, map_derivTop h'.xi, hDab⟩
        Subgroup.normal_top
        (Subgroup.map_top_of_surjective _ h'.xi.surjective)
        le_top
        (derivTop_ne_top h.isPGroup)
        (by
          intro E _ hEinv hDE _
          refine eq_or_top_of_le_of_card_sq_aux h hξ hDE ?_ hc
          rwa [h'xi] at hEinv)
        (by rw [← sqSub_eq, hP2])
        rfl
    -- `(P')^(2) = 1`, so `Z(P) = 1`
    have hbot : Work.Higman.powSub (derivTop P) 2 = ⊥ := by
      rw [eq_bot_iff, Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.mem_bot.mpr (by simpa [pow_two] using hexpD x hx)
    have hZbot : Subgroup.center P = ⊥ := by rw [← hsq2, hbot]
    have hcard1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
      rw [← hZom, hZbot]
      simp
    have h4 := h.omega1_card_ge_four
    omega
  · -- ## `|P'| = |Z|³`: `P' = P` is impossible for a nontrivial finite `2`-group
    have hDtop : derivTop P = ⊤ :=
      Subgroup.eq_top_of_card_eq (derivTop P) (by rw [hc, ← hξ.card_cube])
    exact derivTop_ne_top h.isPGroup hDtop

end Work.Higman.LayersAlt
