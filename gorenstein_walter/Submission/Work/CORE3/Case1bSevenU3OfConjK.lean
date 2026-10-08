import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SevenHints
import Submission.Work.CORE3.SevenConjK
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.J4.J4U3ThreeDvd
import Submission.Work.CORE3.J4.J4U3CentralizerOdd
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.SevenNoInvolCentralizer

/-!
# `Work.CORE3.Case1bSevenU3OfConjK`

Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70**, §3, p. 224, (7),
first conclusion `|U| = k = 3`, in the `g`-form isolated in `Submission/Work/CORE3/J4/J4U3.lean`
(`J4U3_of_conj_K`): with `V = O₂(Ĥ)`, `U = O(Ĥ)`, an involution `y ∉ Ĥ` inverting a nontrivial
odd-order `X ≤ Ĥ` with `|C_G(X)|`, `|N_G(X)|` even, and `g` with `X ≤ K^g`,
`N_G(X) ≤ Ĥ^g` (`K = D.K` the Hall subgroup of `F(U)`), one must show `|U| = 3`.

## State of this file

The target is the known *gap* of Bender's step (7): the printed argument
(`F(U) ⊆ C_Ĥ(X) ≤ N_Ĥ(X) ≤ Ĥ^g`, `V^g ≰ Ĥ` ⇒ `C_{Ĥ^g}(V^g) = 1` ⇒ `|F(U)| = 3`) is defective
(the displayed centralizer is `(VU)^g ≠ 1`); the reconstruction has so far resisted every
attempt recorded in `Submission/Work/CORE3/NOTES_CosetInvCountNeSix.md`,
`Submission/Work/CORE3/J4/NOTES_GDo_CardU3.md`,
`Submission/Work/CORE3/C3six/NOTES_CardUThreeLocal.md` and
`Submission/Work/CORE3/NOTES_Case1bSevenU3OfConjK.md`.

Neighbouring proved pieces (fleet + this area), all sorry-free:
`Work.CORE3.Case1bCentralizingSum` (`Σ_{s ∈ Ĥ∩J} c(s) = 9 + 24|K|`),
`Work.CORE3.Case1bCosetContributionSmall` and `Work.CORE3.Case1bCosetContributionSix`
(the per-coset contributions `0, 2, 0` and `18` for `n = 1, 2, 3, 6`), and
`Work.CORE3.LcFailsCaseAbelian` (case one of the witness construction for `|U| ≠ 3`).

What this file *does* contain (sorry-free) is the first correct step of the reconstruction:

* `involution_mem_conjSub_pcore_of_mem_centralizer`: in the situation of the target, **every
  involution of `C_G(X)` lies in `V^g = conjSub g (O₂(Ĥ))`**.  Indeed, an involution
  `z ∈ C_G(X)` lies in `N_G(X) ≤ Ĥ^g`; if `z ∉ V^g` then the conjugate of `Case1bData.inv`
  gives `D.K^g = invSet_{U^g}(z)`, so `z` inverts every element of `K^g`; but `X ⊆ K^g` is
  centralized by `z` (as `z ∈ C_G(X)`), and an element of `X` has order `3 ≠ 2`.
* `exists_involution_mem_conjSub_pcore_notMem_Hhat`: consequently `V^g ⊄ Ĥ` — the first
  assertion of Bender's displayed argument, and the only part of it that survives as printed.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **An involution of `C_G(X)` lies in `V^g = conjSub g (O₂(Ĥ))`.**

Setting as in the target: `V = O₂(Ĥ)` is a four-group, `K = D.K` the Hall subgroup of `U = O(Ĥ)`
with `I_U(s) = K` for every involution `s ∈ Ĥ ∖ V`, `X ≤ Ĥ` nontrivial of odd order inverted by
the involution `y ∉ Ĥ`, `|C_G(X)|` even, and `X ≤ K^g`, `N_G(X) ≤ Ĥ^g`.

Then every involution `z ∈ C_G(X)` is conjugate (by `g`) into `V`: `z ∈ conjSub g V = O₂(Ĥ^g)`.

Indeed `z ∈ N_G(X) ≤ Ĥ^g`; if `z ∉ V^g` then `z` acts on `U^g = O(Ĥ^g)` with inverted set
`K^g = conjSub g D.K` (conjugate of `Case1bData.inv`), hence inverts `x ∈ X ⊆ K^g`, while
`z ∈ C_G(X)` centralizes `x`.  As `orderOf x = 3`, this forces `x = 1`, contradiction. -/
theorem involution_mem_conjSub_pcore_of_mem_centralizer
    (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hNg : Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat)
    {z : G} (hz2 : orderOf z = 2) (hzC : z ∈ Subgroup.centralizer (X : Set G)) :
    z ∈ Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) := by
  classical
  -- the involution `s = g⁻¹ z g ∈ Ĥ`
  set Vg : Subgroup G := Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) with hVg
  set Kg : Subgroup G := Work.GW2.conjSub g D.K with hKg
  by_contra hzVg
  -- `z` lies in `Ĥ^g` because `z ∈ N_G(X)`
  have hzN : z ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ hzC
  have hzHg : z ∈ Work.GW2.conjSub g B.Hhat := hNg hzN
  -- the conjugate involution `s = g⁻¹ z g ∈ Ĥ`, of order two
  have hsH : g⁻¹ * z * g ∈ B.Hhat := Work.CORE2A.mem_conjSub_iff.mp hzHg
  have hzsq : z * z = 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self z).mp hz2).1
  have hz1 : z ≠ 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self z).mp hz2).2
  have hssq : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzsq]; group
  have hs1 : g⁻¹ * z * g ≠ 1 := by
    intro hone
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [hone]; group
  have hs2 : orderOf (g⁻¹ * z * g) = 2 :=
    (Work.CORE3.orderOf_eq_two_iff_mul_self _).mpr ⟨hssq, hs1⟩
  -- `s ∉ V` (else `z ∈ V^g`)
  have hsV : g⁻¹ * z * g ∉ Work.GW2.pCoreIn 2 B.Hhat := by
    intro hs
    apply hzVg
    rw [hVg, Work.CORE2A.mem_conjSub_iff]
    show g⁻¹ * z * g ∈ Work.GW2.pCoreIn 2 B.Hhat
    exact hs
  -- Bender's `Case1bData.inv` for `s`, `K = invSet B.U s`
  have hKset : (D.K : Set G) = Work.GW2.invSet B.U (g⁻¹ * z * g) :=
    D.inv (g⁻¹ * z * g) hsH hs2 hsV
  -- `K^g` is inverted by `z`
  have hKinv : ∀ w ∈ Kg, z * w * z⁻¹ = w⁻¹ := by
    intro w hw
    have hkw : g⁻¹ * w * g ∈ D.K :=
      Work.CORE2A.mem_conjSub_iff.mp (by rwa [hKg] at hw)
    have hinv : (g⁻¹ * z * g) * (g⁻¹ * w * g) * (g⁻¹ * z * g)⁻¹ = (g⁻¹ * w * g)⁻¹ := by
      have hmem : g⁻¹ * w * g ∈ Work.GW2.invSet B.U (g⁻¹ * z * g) := by
        rw [← hKset]; exact hkw
      exact hmem.2
    calc z * w * z⁻¹
        = g * ((g⁻¹ * z * g) * (g⁻¹ * w * g) * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * w * g)⁻¹ * g⁻¹ := by rw [hinv]
      _ = (g * (g⁻¹ * w * g) * g⁻¹)⁻¹ := by group
      _ = w⁻¹ := by group
  -- a generator of `X`, of order three, lying in `K^g`
  obtain ⟨x, hxX, hx3, hxp, hxVU⟩ := J4.exists_zpowers_eq I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
  have hxKg : x ∈ Kg := hK hxX
  -- `z` centralizes `x` but inverts it
  have hzx : z * x * z⁻¹ = x := by
    have hcomm : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hzC) x hxX
    rw [← hcomm]; group
  have hzx' : z * x * z⁻¹ = x⁻¹ := hKinv x hxKg
  have hxinv : x = x⁻¹ := by rw [hzx'] at hzx; exact hzx.symm
  have hx2 : x * x = 1 := inv_eq_iff_mul_eq_one.mp hxinv.symm
  have hdvd : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hx2
  rw [hx3] at hdvd
  exact absurd hdvd (by norm_num)

/-- **`V^g ⊄ Ĥ`**: the conjugated four-group `O₂(Ĥ^g)` is not contained in `Ĥ`.

This is the assertion of Bender's displayed proof of (7) that survives as printed.  It follows
from the previous lemma together with the fact that the involution witness of `Even |C_G(X)|`
cannot lie in `Ĥ` (`Work.CORE3.SevenNoInvolCentralizer`). -/
theorem exists_involution_mem_conjSub_pcore_notMem_Hhat
    (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hNg : Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat) :
    ∃ z ∈ Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat), z ∉ B.Hhat := by
  classical
  obtain ⟨z, hzC, hz2⟩ := Work.CORE3.exists_involution_mem_of_even_card _ hC
  have hzH : z ∉ B.Hhat := fun hmem =>
    Work.CORE3.SevenNoInvolCentralizer G I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
      ⟨z, hmem, hz2, fun x hx => ((Subgroup.mem_centralizer_iff.mp hzC) x hx).symm⟩
  exact ⟨z, involution_mem_conjSub_pcore_of_mem_centralizer G I hBc B h1 D hy2 hyH hXH hXne
    hXodd hinv hC g hK hNg hz2 hzC, hzH⟩

/-- **`X` is conjugate into the Hall subgroup `K = D.K ≤ F(U)`**: `conjSub g⁻¹ X ≤ D.K`.

Immediate from `hK : X ≤ conjSub g D.K`, but the form in which Bender's (7) uses it (and the
form in which the next corollary needs it). -/
theorem conjSub_inv_le_K (G : Type) [Group G] [Finite G] {X : Subgroup G} {g : G}
    {K : Subgroup G} (hK : X ≤ Work.GW2.conjSub g K) :
    Work.GW2.conjSub g⁻¹ X ≤ K := by
  intro a ha
  have ha' : g * a * g⁻¹ ∈ X := by
    have h := Work.CORE2A.mem_conjSub_iff.mp ha
    simpa using h
  have h2 : g * a * g⁻¹ ∈ Work.GW2.conjSub g K := hK ha'
  have h3 : g⁻¹ * (g * a * g⁻¹) * g ∈ K := Work.CORE2A.mem_conjSub_iff.mp h2
  have h3' : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  rwa [h3'] at h3

/-- **`3 ∣ |K|` in the target's situation**: a conjugate of `X` (of order `3`) lies in `K`. -/
theorem three_dvd_card_K (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K) :
    3 ∣ Nat.card D.K := by
  have hX3 : Nat.card X = 3 := J4.card_X_eq_three I hBc B h1 D hy2 hyH hXH hXne hXodd hinv
  have hle : Work.GW2.conjSub g⁻¹ X ≤ D.K := conjSub_inv_le_K (G := G) hK
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Work.CORE2A.card_conjSub, hX3] at hdvd

/-- **The isolated remaining content of Bender's (7)**, in the "local control fails" form:

if in subcase `(1b)` the odd core `U = O(Ĥ) = O(H)` has order `≠ 3`, then some nontrivial
subgroup `Y` of `F(U) = fittingIn B.U` has normalizer *outside* `Ĥ` — i.e. Bender's local control
(the second conjunct of `Case1 B`) necessarily fails.

This is the exact statement isolated in `Submission/Work/CORE3/NOTES_Case1bSevenU3OfConjK.md`
(and, under the name `Work.CORE3.SevenCardU_lcFails`, also stated — still as a stub — in
`Submission/Work/CORE3/SevenCardU_lcFails.lean`).  Proving it is precisely the reconstruction of
Bender's p. 224 paragraph, whose printed proof is defective.  Note that its *conclusion* is
itself a contradiction with simplicity (`Ĥ` is a coatom, so `N_G(Y) ≰ Ĥ` forces `Y ⊴ G`).

The next theorem shows that the target is nothing but this lemma plus local control. -/
theorem Case1bLcFails (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case1bData B) (hU : Nat.card B.U ≠ 3) :
    ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ Work.GW2.fittingIn B.U ∧
      ¬ (Subgroup.normalizer (Y : Set G) ≤ B.Hhat) := by
  sorry

/-- **The complete reduction.**  The target follows from `Case1bLcFails` in one line: a nontrivial
`Y ≤ F(U)` with `N_G(Y) ≰ Ĥ` contradicts Case (1)'s local control `h1.2`. -/
theorem Case1bSevenU3OfConjK_of_lcFails (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (hlcf : Nat.card B.U ≠ 3 → ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ Work.GW2.fittingIn B.U ∧
      ¬ (Subgroup.normalizer (Y : Set G) ≤ B.Hhat)) :
    Nat.card B.U = 3 := by
  by_contra hU
  obtain ⟨Y, hYne, hYle, hYnotle⟩ := hlcf hU
  exact hYnotle (h1.2 Y hYne hYle)

theorem Case1bSevenU3OfConjK (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hNg : Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat) :
    Nat.card B.U = 3 :=
  Case1bSevenU3OfConjK_of_lcFails G B h1 (fun hU => Case1bLcFails G I hBc B D hU)

end Work.CORE3
