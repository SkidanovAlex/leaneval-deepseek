import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.RedAux.setup
import Submission.Work.Higman.RedAux.deriv_eq_sq_false
import Submission.Work.Higman.RedAux.class_two_cover_false
import Submission.Work.Higman.RedAux.c4_reduction
import Submission.Work.Higman.RedAux.c4_endgame

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-!
# `Work.Higman.reducible_aux` — the reducible case of the `C₄` exclusion

`P` is a Suzuki 2-group and `A ⊴ P` is a `ξ`-invariant abelian normal subgroup with
`Ω₁(P) ≤ A`, `[P,P] = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)` and
`|A| = |Ω₁(P)|²`.  If in addition `P/A` is *reducible* — there is a `ξ`-invariant normal subgroup
strictly between `A` and `P` — then this is contradictory (`C₄` is excluded).

The extra hypothesis is not needed for the *mathematics* to be contradictory: the general `C₄`
exclusion `H8.c4_exclusion` (Higman 1963, Theorem 1 / §4 Lemma 6, §5 Lemma 8) applies to a
**maximal** `ξ`-invariant abelian normal subgroup.  The work here is to show that the given `A`
is maximal (`maximal_of_c4_data`): if `B ⊇ A` is `ξ`-invariant abelian normal, then `B² ⊆ A`
(every square of `P` lies in `A`) and `B² ⊇ A²`, so by the trichotomy for `ξ`-invariant subgroups
of `A` (`H8.c4_xi_inv_sub_trichotomy`) `B² ∈ {A², A}`; the case `B² = A` is excluded by Higman's
Lemma 9 (`Work.Higman.powSub_four_bot_of_maximal'`: a maximal `ξ`-invariant abelian normal
subgroup has exponent dividing `4`, hence `B⁴ = 1`, but `B⁴ = (B²)² = A² = Ω₁(P) ≠ 1`), and the
case `B² = A²` forces `|B| = |B ⊓ Ω₁(P)| · |B²| = |Ω₁(P)| · |A²| = q² = |A|`, i.e. `B = A`
(`card_le_of_abelian_of_sq_eq`).
-/

/-- A subgroup of exponent two is abelian. -/
theorem commutator_eq_bot_of_sq_eq_bot {C : Subgroup P}
    (hC2 : Work.Higman.powSub C 2 = ⊥) : ⁅C, C⁆ = ⊥ := by
  have hsq : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    have hmem : x ^ 2 ∈ (⊥ : Subgroup P) := by
      rw [← hC2]; exact pow_mem_powSub (n := 2) hx
    simpa [pow_two] using Subgroup.mem_bot.mp hmem
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx' : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
      _ = x⁻¹ * (x * x) := by rw [hsq x hx]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hy' : y⁻¹ = y := by
    calc y⁻¹ = y⁻¹ * 1 := (mul_one _).symm
      _ = y⁻¹ * (y * y) := by rw [hsq y hy]
      _ = y := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hxy : (x * y)⁻¹ = x * y := by
    calc (x * y)⁻¹ = (x * y)⁻¹ * 1 := (mul_one _).symm
      _ = (x * y)⁻¹ * ((x * y) * (x * y)) := by rw [hsq (x * y) (C.mul_mem hx hy)]
      _ = x * y := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  calc y * x = y⁻¹ * x⁻¹ := by rw [hy', hx']
    _ = (x * y)⁻¹ := (mul_inv_rev x y).symm
    _ = x * y := hxy

/-- **Counting lemma.**  Let `E` be abelian with `E² = A²`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`.
Squaring is a homomorphism `E → A` whose kernel is `E ⊓ Ω₁(P) = A²` and whose image lies in
`E² = A²`; hence `|E| = |E²| · |image| ≤ |A²|² = |A|`.  (Applied to an abelian `B ⊇ A` with
`B² = A²` it gives `B = A`.) -/
theorem card_le_of_abelian_of_sq_eq (h : IsSuzuki2Grp P) {A E : Subgroup P}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    Nat.card ↥E ≤ Nat.card ↥A := by
  classical
  have hA2le : Work.Higman.powSub A 2 ≤ A := powSub_le (by norm_num)
  have hA2E : Work.Higman.powSub A 2 ≤ E := hE2 ▸ powSub_le (by norm_num)
  -- the squaring map `↥E →* ↥A`
  let φ : ↥E →* ↥A :=
    { toFun := fun x => ⟨(x : P) * (x : P), by
        have hmem : (x : P) ^ 2 ∈ Work.Higman.powSub E 2 := pow_mem_powSub (n := 2) x.2
        rw [hE2] at hmem
        exact hA2le (by simpa [pow_two] using hmem)⟩
      map_one' := by
        ext
        show (1 : P) * 1 = 1
        simp
      map_mul' := fun x y => by
        ext
        show (((x * y : ↥E)) : P) * (((x * y : ↥E)) : P)
            = (x : P) * (x : P) * ((y : P) * (y : P))
        rw [Subgroup.coe_mul]
        have hc : (x : P) * (y : P) = (y : P) * (x : P) := hEab (x : P) x.2 (y : P) y.2
        calc (x : P) * (y : P) * ((x : P) * (y : P))
            = (x : P) * ((y : P) * (x : P)) * (y : P) := by group
          _ = (x : P) * ((x : P) * (y : P)) * (y : P) := by rw [hc]
          _ = (x : P) * (x : P) * ((y : P) * (y : P)) := by group }
  have hcardE : Nat.card ↥E = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker : Subgroup ↥E)
    have h2 : Nat.card (↥E ⧸ φ.ker) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [h2, mul_comm] at h1
    exact h1
  -- the kernel is `A ^ (2)` (viewed inside `E`)
  have hker : φ.ker = (Work.Higman.powSub A 2).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx2 : (x : P) ^ 2 = 1 := by
        have hc := congrArg (fun y : ↥A => (y : P)) hx
        simpa [φ, pow_two] using hc
      have hom : (x : P) ∈ Work.Higman.omega1 P := h.mem_omega1.mpr hx2
      rw [← htop] at hom
      exact hom
    · intro hx
      have hom : (x : P) ∈ Work.Higman.omega1 P := by rw [← htop]; exact hx
      have hx2 : (x : P) ^ 2 = 1 := h.mem_omega1.mp hom
      show φ x = 1
      apply Subtype.ext
      simpa [φ, pow_two] using hx2
  have hkerCard : Nat.card ↥φ.ker = Nat.card ↥(Work.Higman.powSub A 2) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2E).toEquiv
  -- the image lies in `E ^ (2) = A ^ (2)`
  have hrangeLe : Nat.card ↥φ.range ≤ Nat.card ↥(Work.Higman.powSub A 2) := by
    have hsub : (φ.range : Set ↥A) ⊆ ((Work.Higman.powSub A 2).subgroupOf A : Set ↥A) := by
      rintro y ⟨x, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hmem : (x : P) ^ 2 ∈ Work.Higman.powSub E 2 := pow_mem_powSub (n := 2) x.2
      rw [hE2] at hmem
      simpa [φ, pow_two] using hmem
    calc Nat.card ↥φ.range
        ≤ Nat.card ↥((Work.Higman.powSub A 2).subgroupOf A) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
            (Subgroup.inclusion_injective hsub)
      _ = Nat.card ↥(Work.Higman.powSub A 2) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2le).toEquiv
  have hA2card : Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥(Work.Higman.omega1 P) := by
    rw [htop]
  calc Nat.card ↥E = Nat.card ↥φ.ker * Nat.card ↥φ.range := hcardE
    _ ≤ Nat.card ↥(Work.Higman.powSub A 2) * Nat.card ↥(Work.Higman.powSub A 2) := by
        rw [hkerCard]
        exact Nat.mul_le_mul_left _ hrangeLe
    _ = Nat.card ↥A := by rw [hA2card, hcard, pow_two]

/-- **The `C₄` data forces `A` to be maximal.**  If `A ⊴ P` is `ξ`-invariant abelian with
`Ω₁(P) ≤ A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`, then `A` is
maximal among the `ξ`-invariant abelian normal subgroups of `P`.

Take a maximal `ξ`-invariant abelian normal `B ⊇ A`.  Its square `B²` lies in `A` (every square of
`P` does) and contains `A²`, so by the trichotomy for `ξ`-invariant subgroups of `A` it is `A²`
or `A`.  If `B² = A` then `B⁴ = A² = Ω₁(P) ≠ 1`, contradicting Higman's Lemma 9 (`B⁴ = 1` for a
maximal `B`, `Work.Higman.powSub_four_bot_of_maximal'`).  Hence `B² = A²`, and then
`|B| = |B ⊓ Ω₁(P)| · |B²| = |Ω₁(P)| · |A²| = q² = |A|`, so `B = A`. -/
theorem maximal_of_c4_data (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A := by
  intro B hB hAB
  -- a maximal `ξ`-invariant abelian normal subgroup `B₀ ⊇ B`, hence `⊇ A`
  have hfin : ({B' : Subgroup P | IsXiAbelNormal h B' ∧ B ≤ B'}).Finite :=
    Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨B₀, hB₀⟩ := hfin.exists_maximal ⟨B, ⟨hB, le_rfl⟩⟩
  obtain ⟨hB₀i, hBB₀⟩ := hB₀.1
  have hAB₀ : A ≤ B₀ := hAB.trans hBB₀
  have hB₀max : ∀ B' : Subgroup P, IsXiAbelNormal h B' → B₀ ≤ B' → B' = B₀ :=
    fun B' hB' hle => le_antisymm (hB₀.2 ⟨hB', hBB₀.trans hle⟩ hle) hle
  -- Higman's Lemma 9: `B₀` has exponent dividing `4`
  have hB₀4 : Work.Higman.powSub B₀ 4 = ⊥ :=
    Work.Higman.powSub_four_bot_of_maximal' h hB₀i hB₀max
  have hB₀ab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := hB₀i.abelian
  -- `A² ≤ B₀²` and `B₀² ≤ A`
  have hA2le : Work.Higman.powSub A 2 ≤ Work.Higman.powSub B₀ 2 := powSub_mono hAB₀
  have hB₀2le : Work.Higman.powSub B₀ 2 ≤ A := by
    rw [powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hB₀2inv : (Work.Higman.powSub B₀ 2).map (h.xi : MulAut P).toMonoidHom =
      Work.Higman.powSub B₀ 2 := map_powSub (h.xi : MulAut P) hB₀i.map_eq 2
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h3 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h5 := h.omega1_card_ge_four
    omega
  -- the trichotomy for `B₀²`
  have hB₀2 : Work.Higman.powSub B₀ 2 = Work.Higman.powSub A 2 := by
    rcases RedAux.red_trichotomy h A (Work.Higman.powSub B₀ 2) hA hA4 hB₀2le hB₀2inv
      with h2 | h2 | h2
    · -- `B₀² = ⊥`, contradicting `A² ≤ B₀²` and `A² ≠ ⊥`
      exact absurd (le_bot_iff.mp (h2 ▸ hA2le)) hA2ne
    · exact h2
    · -- `B₀² = A`: then `B₀⁴ = A² = Ω₁(P) ≠ ⊥`, contradicting Higman's Lemma 9
      exfalso
      have h4 : Work.Higman.powSub B₀ 4 = Work.Higman.powSub A 2 := by
        rw [← Work.Higman.powSub_powSub hB₀ab 2 2, h2]
      rw [hB₀4] at h4
      exact hA2ne h4.symm
  -- counting: `|B₀| ≤ |A|`, and `A ≤ B₀`, so `B₀ = A`
  have hle : Nat.card ↥B₀ ≤ Nat.card ↥A :=
    card_le_of_abelian_of_sq_eq h hB₀ab hB₀2 htop hcard
  have hB₀A : A = B₀ := Subgroup.eq_of_le_of_card_ge hAB₀ hle
  exact le_antisymm (hBB₀.trans (le_of_eq hB₀A.symm)) hAB

/-- **The `C₄`-shape is excluded when `P / A` is reducible** (Higman 1963, Lemma 8 / §4
Lemma 6).  Same hypotheses as `Work.Higman.no_square_maximal`, together with the existence of a
`ξ`-invariant normal subgroup strictly between `A` and `P`. -/
theorem reducible_aux {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : commutator P = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hnirr : ¬ (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D = A ∨ D = ⊤)) :
    False := by
  have hEnd : RedAux.c4Endgame := by
    intro P' _ _ h' A' C' hA' hNA' hGs' hsq' hA4' htop' hcard' hCn' hCinv' hAC' hCA'
      hcover' hCd' hC2' hCP' hACd'
    exact RedAux.c4_endgame h' hA' hNA' hGs' hsq' hA4' htop' hcard' hCn' hCinv' hAC' hCA'
      hcover' hCd' hC2' hCP' hACd'
  exact RedAux.reducible_aux_of_endgame hEnd h hAxi hAab hNA hGs hsq hA4 htop hcard hnirr

end Work.Higman
