/-
Area BG, Theorem 4.3, case (a): `Work.GW2.C23.CaseAProp` (T43-A).

If `μ ∈ 𝒮₄(C)` has a hat `μ̂` which is not fixed by `N_G(S)`, then every `ν` in the component
of `μ` in the graph `Δ` satisfies the triple pattern `TripleAt` (Bender–Glauberman 1981,
Theorem 4.3, case (a), pp. 212–213).

Outline (all inputs are proved elsewhere in the area; the two non-trivial group-theoretic inputs
of `N_G(S)`-orbit theory are isolated in `caseA_main`'s hypotheses):

* `HatProp` (`BG/Hat`) gives the hat `ν̂` of `ν ∈ 𝒮₄(C)`, `HatInjProp` (`BG/hatInj`) its
  injectivity, and `NOrbProp` (`BG/nOrb`, assembled here as `caseA_NOrbProp` from the group
  inputs `caseA_nOrbGroup` and `l41vBInv`) describes the `N_G(S)`-orbit of a non-fixed hat `θ`:
  exactly three pairwise distinct conjugates `θ, θ₂, θ₃`, and every conjugate is one of them;
* `L41vProp` (`BG/l41v`) says the hat-set of `𝒮'(χ) = bset' C β₂ χ` is `N_G(S)`-invariant; with
  the orbit of `θ` this puts `θ, θ₂, θ₃` in the hat-set of `𝒮'(χ₀)` for `χ₀` in the support `T`
  of `δ_μ` (four elements, DELTA-SHAPE, `BG/deltaShape`), and with the bound `|𝒮'(χ)| ≤ 3`
  (`caseA_bset'_ncard_le_three`, from `l41_iff` — Lemma 4.1 (i) — Theorem 3.2 and the
  finiteness of `𝒮(χ)`) it identifies `𝒮'(χ) = {μ, μ₂, μ₃}` for every `χ ∈ T`;
* hence `δ_μ, δ_{μ₂}, δ_{μ₃}` all have support `T` with `±1` coefficients, and the Brauer–Suzuki
  Gram matrix (`Work.BG.s02_gram`) shows that distinct members of `𝒮₄(C)` have orthogonal `δ`'s;
  the three integer coefficient vectors are therefore pairwise orthogonal `±1`-vectors on a
  4-set, and `HadamardProp` (`BG/hadamard`) — applied with each of the three as base — gives the
  sign patterns `(+,+,+,+)`, `(+,-,+,-)`, `(+,+,-,-)`;
* orthogonality also shows that every `δ` adjacent to a member of the triple shares a constituent
  with it, hence lies in `𝒮'(χ) = {μ, μ₂, μ₃}`: the component of `μ` is exactly the triple;
* the hats of the triple are pairwise `N_G(S)`-conjugate (they are `θ, θ₂, θ₃`) and
  `N_G(S)` normalises `B` (`BG/l41vBInv`), so `NSConj` behaves as an equivalence relation on
  them (`caseA_NSConj_symm`, `caseA_NSConj_trans`).

`caseA_main` carries the two remaining inputs (`NOrbProp` and the bound `|𝒮'(χ)| ≤ 3`) as
explicit hypotheses; `caseA` discharges them.
-/
import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.Sec4Extra
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.hatInj
import Submission.Work.BG.hadamard
import Submission.Work.BG.deltaShape
import Submission.Work.BG.nOrb
import Submission.Work.BG.l41v
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.Hat
import Submission.Work.BG.caseA_lemma41coherent
import Submission.Work.BG.s02_gram
import Submission.Work.BG.L41Aux
import Submission.Work.BG.l41vBInv
import Submission.Work.BG.caseA_l41iff
import Submission.Work.BG.normFourPmIrr
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.nOrbBInv
import Submission.Work.BG.nOrbCosets

namespace Work.BG.thm43

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

attribute [local instance] Classical.propDecidable

/-! ## The index `|N_G(S) : C_G(S)|` (used for `NOrbProp`) -/

/-- An automorphism of `V` is determined by its permutation of the non-identity elements, and
these are already permuted among themselves; so `MulAut V` embeds in `Perm Ω` with
`Ω = {v : V // v ≠ 1}`. -/
noncomputable def caseA_mulAutNonidHom {G : Type} [Group G] (V : Subgroup G) :
    MulAut ↥V →* Equiv.Perm {v : ↥V // v ≠ 1} where
  toFun e :=
    { toFun := fun w => ⟨e w.1, fun h => w.2 ((MulEquiv.map_eq_one_iff e).mp h)⟩
      invFun := fun w => ⟨e.symm w.1, fun h => w.2 ((MulEquiv.map_eq_one_iff e.symm).mp h)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  map_one' := by ext w; rfl
  map_mul' := fun a b => by ext w; rfl

/-- `caseA_mulAutNonidHom` is injective (an automorphism fixing every non-identity element is the
identity). -/
theorem caseA_mulAutNonidHom_ker {G : Type} [Group G] (V : Subgroup G) :
    (caseA_mulAutNonidHom V).ker = ⊥ := by
  ext e
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro h
    ext v
    by_cases hv : v = 1
    · subst hv; simp
    · have h1 := congrArg (fun (p : Equiv.Perm {v : ↥V // v ≠ 1}) =>
        ((p ⟨v, hv⟩ : {v : ↥V // v ≠ 1}) : ↥V)) h
      simpa [caseA_mulAutNonidHom] using h1
  · intro h; subst h; simp

/-- `|Aut V| ∣ 6` for a group `V` of order `4`, because `V` has exactly three non-identity
elements and an automorphism is determined by its action on them. -/
theorem caseA_cardMulAutDvdSix {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : Nat.card ↥V = 4) : Nat.card (MulAut ↥V) ∣ 6 := by
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  have hΩ : Nat.card {v : ↥V // v ≠ 1} = 3 := by
    haveI : Fintype {v : ↥V // v ≠ 1} := Fintype.ofFinite _
    haveI : Fintype {v : ↥V // v = 1} := Fintype.ofFinite _
    have hV' : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (fun v : ↥V => v = 1)]
    have hone : Fintype.card {v : ↥V // v = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨1, rfl⟩, fun a => Subtype.ext a.2⟩
    rw [hone, hV']
  have hker : (caseA_mulAutNonidHom V).ker = ⊥ := caseA_mulAutNonidHom_ker V
  have h1 : Nat.card (MulAut ↥V) = Nat.card ↥((caseA_mulAutNonidHom V).range) := by
    rw [← Subgroup.index_bot, ← hker, Subgroup.index_ker]
  have h2 : Nat.card ↥((caseA_mulAutNonidHom V).range)
      ∣ Nat.card (Equiv.Perm {v : ↥V // v ≠ 1}) :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (Equiv.Perm {v : ↥V // v ≠ 1}) = 6 := by
    rw [Nat.card_perm, hΩ]
    norm_num
  rw [h1]
  exact dvd_trans h2 (by rw [h3])

/-- For a subgroup `V` of order `4`, `|N_G(V) : C_G(V)| ∣ 6`: conjugation embeds
`N_G(V)/C_G(V)` in `Aut(V)`. -/
theorem caseA_indexDvdSix {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : Nat.card ↥V = 4) :
    (Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G)) ∣ 6 := by
  rw [Subgroup.relIndex, ← Subgroup.normalizerMonoidHom_ker V, Subgroup.index_ker]
  exact dvd_trans (Subgroup.card_subgroup_dvd_card _) (caseA_cardMulAutDvdSix V hV)

/-- For a commutative Sylow `2`-subgroup `S`, `|N_G(S) : C_G(S)|` is odd: `S ≤ C_G(S) ≤ N_G(S)`
and `|N_G(S) : C_G(S)|` divides `|N_G(S) : S|`, which divides the odd number `|G : S|`. -/
theorem caseA_indexOdd {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x) :
    Odd ((Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((S : Subgroup G) : Set G))) := by
  set V : Subgroup G := (S : Subgroup G) with hVdef
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hNdef
  have hSC : V ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hVN : V ≤ N := le_trans hSC (Subgroup.centralizer_le_normalizer (V : Set G))
  have hdvd1 : (C.subgroupOf N).index ∣ (V.subgroupOf N).index :=
    Subgroup.index_dvd_of_le (H := V.subgroupOf N) (K := C.subgroupOf N) (fun x hx => hSC hx)
  have hdvd2 : (V.subgroupOf N).index ∣ V.index :=
    ⟨N.index, (Subgroup.relIndex_mul_index hVN).symm⟩
  have hoddV : Odd V.index := by
    refine Nat.not_even_iff_odd.mp ?_
    rw [even_iff_two_dvd]
    exact S.not_dvd_index
  exact hoddV.of_dvd_nat (dvd_trans hdvd1 hdvd2)

/-! ## The group-theoretic input of `NOrbProp` (`N_G(S)`-orbit theory) -/

/-- **Group-theoretic input for `NOrbProp` when `D.n = 2`** (`S ≅ V₄`): `C_G(S)` acts on `B`
by *inner* automorphisms of `B`; the cube of every element of `N_G(S)` lies in `C_G(S)`; and
`N_G(S)` is covered by the three cosets `C_G(S)`, `x C_G(S)`, `x² C_G(S)` for any
`x ∈ N_G(S) ∖ C_G(S)`.

The first clause is `Work.BG.nOrbBInv`.  For the other two, `N_G(S)/C_G(S)` embeds in
`Aut(S) ≅ S₃` (`Work.BG.thm43.indexDvdSix`) and has odd order because `S ≤ C_G(S) ≤ N_G(S)`
and `S` is a Sylow `2`-subgroup (`Work.BG.thm43.indexOdd`); so `|N_G(S) : C_G(S)| ∣ 3`, and
the quotient of order `1` or `3` gives the cube condition and the coset covering
(`Work.BG.nOrbCosetIndexThree`). -/
theorem caseA_nOrbGroup {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) ∧
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
      ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set V : Subgroup G := (D.S : Subgroup G) with hVdef
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hNdef
  set Cc : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  have hcard : Nat.card ↥V = 4 := Work.BG.BGData_isFourGroup D hn |>.1
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := Work.BG.BGData_S_comm D hn
  have hidx6 : (Cc.subgroupOf N).index ∣ 6 := caseA_indexDvdSix V hcard
  have hodd : Odd ((Cc.subgroupOf N).index) := caseA_indexOdd D.S hcomm
  have hidx3 : (Cc.subgroupOf N).index ∣ 3 := by
    have hidx6' : (Cc.subgroupOf N).index ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hidx6
    exact hodd.coprime_two_right.dvd_mul_left.mp hidx6'
  have hcases : (Cc.subgroupOf N).index = 1 ∨ (Cc.subgroupOf N).index = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hidx3
  refine ⟨(Work.BG.nOrbBInv D hn).2, ?_, ?_⟩
  · intro x hxN
    have hmem : (⟨x, hxN⟩ : ↥N) ^ 3 ∈ Cc.subgroupOf N := by
      rcases hcases with h1 | h3
      · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      · rw [← h3]; exact Subgroup.pow_index_mem (Cc.subgroupOf N) ⟨x, hxN⟩
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  · intro x hxN hxC y hyN
    rcases hcases with h1 | h3
    · left
      have hmem : (⟨y, hyN⟩ : ↥N) ∈ Cc.subgroupOf N := by
        rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    · have hxN' : (⟨x, hxN⟩ : ↥N) ∉ Cc.subgroupOf N := by
        intro h
        exact hxC (by simpa using (Subgroup.mem_subgroupOf.mp h))
      rcases Work.BG.nOrbCosetIndexThree (Cc.subgroupOf N) h3 hxN' ⟨y, hyN⟩ with
        hmem | ⟨c, hc, hce⟩ | ⟨c, hc, hce⟩
      · left
        simpa using (Subgroup.mem_subgroupOf.mp hmem)
      · right; left
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce
      · right; right
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce


/-- Two distinct irreducible characters are orthogonal. -/
theorem caseA_inner_irr_eq_zero {a b : ClassFunction G ℂ}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b) (hne : a ≠ b) :
    ClassFunction.inner a b = 0 := by
  rw [irr_cf_inner (mem_irreducibleCharacters.mpr ha) (mem_irreducibleCharacters.mpr hb),
    ite_eq_right hne]

/-- `λ₂ * μ ∉ S4Index` for `μ ∈ S4Index`: its value at `t` is the negative of its degree. -/
theorem caseA_lam_two_notMem_S4Index (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    {μ : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ S4Index C) :
    lamCF C β₂ * μ ∉ S4Index C := by
  intro hmem
  obtain ⟨hirrμ, -, htμ⟩ := hμ
  obtain ⟨-, -, ht⟩ := hmem
  have ht' : (lamCF C β₂ * μ) C.t = -μ C.t := lam_two_mul_apply_t C h2 hβ μ
  have hlam1 : lamCF C β₂ (1 : ↥C.P.H0) = 1 := by
    simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  have hone : (lamCF C β₂ * μ) 1 = μ 1 := by
    rw [ClassFunction.mul_apply, hlam1, one_mul]
  rw [ht', htμ, hone] at ht
  have : (2 : ℂ) * μ 1 = 0 := by linear_combination (-1) * ht
  exact irr_apply_one_ne_zero C hirrμ ((mul_eq_zero.mp this).resolve_left (by norm_num))

/-- Distinct members of `S4Index C` have orthogonal `δ`'s (in the `|S| = 4` case). -/
theorem caseA_delta_orth (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2) {β₂ : quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {ν μ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ S4Index C) (hμ : μ ∈ S4Index C)
    (hne : μ ≠ ν) :
    ClassFunction.inner (delta C β₂ ν) (delta C β₂ μ) = 0 := by
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  obtain ⟨hirrν, hsconjν, htν⟩ := hν
  obtain ⟨hirrμ, hsconjμ, htμ⟩ := hμ
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  have hlam2 : IsIrreducibleCharacter (lamCF C β₂ * ν) := lam_two_mul_irr C hirrν
  have hlam2μ : IsIrreducibleCharacter (lamCF C β₂ * μ) := lam_two_mul_irr C hirrμ
  have hne_nu : lamCF C β₂ * ν ≠ ν := lam_two_mul_ne_self C h2 hβ hirrν
  have hne_mu : lamCF C β₂ * μ ≠ μ := lam_two_mul_ne_self C h2 hβ hirrμ
  have hfixν : sconj C (lamCF C β₂ * ν) = lamCF C β₂ * ν := by
    rw [sconj_lam_two_mul C h2 hβ, hsconjν]
  have hfixμ : sconj C (lamCF C β₂ * μ) = lamCF C β₂ * μ := by
    rw [sconj_lam_two_mul C h2 hβ, hsconjμ]
  have hνμ : ν ≠ μ := fun h => hne h.symm
  have hν_lamμ : ν ≠ lamCF C β₂ * μ := by
    intro h
    exact caseA_lam_two_notMem_S4Index C h2 hβ ⟨hirrμ, hsconjμ, htμ⟩ (h ▸ (⟨hirrν, hsconjν, htν⟩ : ν ∈ S4Index C))
  have hlamν_μ : lamCF C β₂ * ν ≠ μ := by
    intro h
    exact caseA_lam_two_notMem_S4Index C h2 hβ ⟨hirrν, hsconjν, htν⟩ (h ▸ (⟨hirrμ, hsconjμ, htμ⟩ : μ ∈ S4Index C))
  have hlam_lam : lamCF C β₂ * ν ≠ lamCF C β₂ * μ := by
    intro h
    apply hne
    have hmul : ∀ φ : ClassFunction ↥C.P.H0 ℂ, lamCF C β₂ * (lamCF C β₂ * φ) = φ := by
      intro φ
      rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
    rw [← hmul ν, ← hmul μ, h]
  have hgram := s02_gram C ν (lamCF C β₂ * ν) μ (lamCF C β₂ * μ)
    hirrν hlam2 hirrμ hlam2μ ⟨β₂, rfl⟩ ⟨β₂, rfl⟩
  simp only [delta]
  rw [hgram]
  have hA : cH C ν μ = 0 := by
    rw [cH_eq_inner_add C hirrν hirrμ, hsconjμ, caseA_inner_irr_eq_zero hirrν hirrμ hνμ]
    ring
  have hB : cH C ν (lamCF C β₂ * μ) = 0 := by
    rw [cH_eq_inner_add C hirrν hlam2μ, hfixμ,
      caseA_inner_irr_eq_zero hirrν hlam2μ hν_lamμ]
    ring
  have hC : cH C (lamCF C β₂ * ν) μ = 0 := by
    rw [cH_eq_inner_add C hlam2 hirrμ, hsconjμ,
      caseA_inner_irr_eq_zero hlam2 hirrμ hlamν_μ]
    ring
  have hD : cH C (lamCF C β₂ * ν) (lamCF C β₂ * μ) = 0 := by
    rw [cH_eq_inner_add C hlam2 hlam2μ, hfixμ,
      caseA_inner_irr_eq_zero hlam2 hlam2μ hlam_lam]
    ring
  rw [hA, hB, hC, hD]
  ring

/-- A virtual character equals the sum of its Fourier series over any index set containing
exactly the irreducibles occurring in it. -/
theorem caseA_eq_sum_of_support {δ : ClassFunction G ℂ} (hZ : δ ∈ ZIrr G)
    (T : Finset (IrreducibleCharacter G))
    (hT : ∀ χ : IrreducibleCharacter G, χ ∈ T ↔
      ClassFunction.inner δ (χ : ClassFunction G ℂ) ≠ 0) :
    δ = ∑ χ ∈ T, ClassFunction.inner δ (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ) := by
  classical
  obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hZ
  have hcoeff : ∀ (a : ClassFunction G ℂ), IsIrreducibleCharacter a →
      ClassFunction.inner δ a = (c a : ℂ) := by
    intro a ha
    rw [hrepr]
    exact inner_eq_coeff_of_repr ⟨a, ha⟩ hsupp
  have himg : c.support =
      T.image (fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ)) := by
    ext a
    constructor
    · intro ha
      have hirr : IsIrreducibleCharacter a := mem_irreducibleCharacters.mp (hsupp ha)
      have hne : ClassFunction.inner δ a ≠ 0 := by
        rw [hcoeff a hirr]
        exact_mod_cast (Finsupp.mem_support_iff.mp ha)
      exact Finset.mem_image.mpr ⟨⟨a, hirr⟩, (hT _).mpr hne, rfl⟩
    · intro ha
      obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp ha
      rw [Finsupp.mem_support_iff]
      intro h0
      have hinner := (hT χ).mp hχ
      rw [hcoeff (χ : ClassFunction G ℂ) χ.isIrreducible, h0] at hinner
      exact hinner (by norm_num)
  have hmid : δ = ∑ χ ∈ T, (c (χ : ClassFunction G ℂ) : ℂ) • (χ : ClassFunction G ℂ) := by
    rw [hrepr, himg]
    exact Finset.sum_image (s := T) (g := fun χ : IrreducibleCharacter G => (χ : ClassFunction G ℂ))
      (f := fun a : ClassFunction G ℂ => (c a : ℂ) • a) (fun a _ b _ h => Subtype.ext h)
  calc δ = ∑ χ ∈ T, (c (χ : ClassFunction G ℂ) : ℂ) • (χ : ClassFunction G ℂ) := hmid
    _ = ∑ χ ∈ T, ClassFunction.inner δ (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ) :=
        Finset.sum_congr rfl fun χ _ => by
          rw [← hcoeff (χ : ClassFunction G ℂ) χ.isIrreducible]

/-- Inner product of two integer combinations of the same family of irreducibles. -/
theorem caseA_inner_eq_sum_coeff (T : Finset (IrreducibleCharacter G))
    (f g : IrreducibleCharacter G → ℤ) {δ ε : ClassFunction G ℂ}
    (hδ : δ = ∑ χ ∈ T, (f χ : ℂ) • (χ : ClassFunction G ℂ))
    (hε : ε = ∑ χ ∈ T, (g χ : ℂ) • (χ : ClassFunction G ℂ)) :
    ClassFunction.inner δ ε = ((∑ χ ∈ T, f χ * g χ : ℤ) : ℂ) := by
  classical
  rw [hδ, hε, inner_sum_left]
  have key : ∀ χ ∈ T, ClassFunction.inner ((f χ : ℂ) • (χ : ClassFunction G ℂ))
      (∑ χ' ∈ T, (g χ' : ℂ) • (χ' : ClassFunction G ℂ)) = (f χ : ℂ) * (g χ : ℂ) := by
    intro χ hχ
    have hsingle : (∑ χ' ∈ T, ClassFunction.inner (χ : ClassFunction G ℂ)
          ((g χ' : ℂ) • (χ' : ClassFunction G ℂ))) =
        ClassFunction.inner (χ : ClassFunction G ℂ) ((g χ : ℂ) • (χ : ClassFunction G ℂ)) :=
      Finset.sum_eq_single_of_mem χ hχ (fun χ' hχ' hne => by
        rw [ClassFunction.inner_smul_right,
          irr_cf_inner χ.mem_irreducibleCharacters χ'.mem_irreducibleCharacters,
          ite_eq_right (fun h => hne (Subtype.ext h).symm), mul_zero])
    rw [ClassFunction.inner_smul_left, inner_sum_right, hsingle,
      ClassFunction.inner_smul_right,
      irr_cf_inner χ.mem_irreducibleCharacters χ.mem_irreducibleCharacters]
    simp
  rw [Finset.sum_congr rfl key]
  have hcast : ((∑ χ ∈ T, f χ * g χ : ℤ) : ℂ) = ∑ χ ∈ T, (f χ : ℂ) * (g χ : ℂ) := by
    push_cast
    ring
  rw [hcast]

/-- Three `\pm 1`-combinations of the same four irreducibles with pairwise orthogonal
coefficient vectors take the sign pattern `(+,+,+,+)`, `(+,-,+,-)`, `(+,+,-,-)` after a
relabelling of the four irreducibles (Hadamard). -/
theorem caseA_hadamard_triple {T : Finset (IrreducibleCharacter G)} (hTcard : T.card = 4)
    (f₁ f₂ f₃ : IrreducibleCharacter G → ℤ) (δ₁ δ₂ δ₃ : ClassFunction G ℂ)
    (hsq : ∀ χ ∈ T, f₁ χ ^ 2 = 1 ∧ f₂ χ ^ 2 = 1 ∧ f₃ χ ^ 2 = 1)
    (h₁ : δ₁ = ∑ χ ∈ T, (f₁ χ : ℂ) • (χ : ClassFunction G ℂ))
    (h₂ : δ₂ = ∑ χ ∈ T, (f₂ χ : ℂ) • (χ : ClassFunction G ℂ))
    (h₃ : δ₃ = ∑ χ ∈ T, (f₃ χ : ℂ) • (χ : ClassFunction G ℂ))
    (ho₁₂ : ∑ χ ∈ T, f₁ χ * f₂ χ = 0) (ho₁₃ : ∑ χ ∈ T, f₁ χ * f₃ χ = 0)
    (ho₂₃ : ∑ χ ∈ T, f₂ χ * f₃ χ = 0) :
    ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction G ℂ,
      IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ IsPmIrr χ₃ ∧ IsPmIrr χ₄ ∧
      δ₁ = χ₁ + χ₂ + χ₃ + χ₄ ∧ δ₂ = χ₁ - χ₂ + χ₃ - χ₄ ∧ δ₃ = χ₁ + χ₂ - χ₃ - χ₄ := by
  classical
  obtain ⟨e, heinj, heT, hb, hc⟩ := hadamard T f₁ f₂ f₃ hTcard hsq ho₁₂ ho₁₃ ho₂₃
  have hTimg : T = Finset.univ.image e := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro χ hχ
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hχ
      exact heT k
    · rw [hTcard, Finset.card_image_of_injective _ heinj, Finset.card_univ, Fintype.card_fin]
  let χk : Fin 4 → ClassFunction G ℂ := fun k => (f₁ (e k) : ℂ) • ((e k) : ClassFunction G ℂ)
  have hsmul : ∀ (a b : ℤ) (x : ClassFunction G ℂ),
      (a : ℂ) • ((b : ℂ) • x) = ((a * b : ℤ) : ℂ) • x := by
    intro a b x
    rw [Int.cast_mul]
    exact smul_smul (a : ℂ) (b : ℂ) x
  have hf₁sq : ∀ χ ∈ T, f₁ χ * f₁ χ = 1 := by
    intro χ hχ
    rw [← sq, (hsq χ hχ).1]
  have step₁ : (∑ χ ∈ T, (f₁ χ : ℂ) • (χ : ClassFunction G ℂ)) = ∑ k : Fin 4, χk k := by
    rw [hTimg, Finset.sum_image (s := Finset.univ) (g := e)
      (f := fun χ : IrreducibleCharacter G => (f₁ χ : ℂ) • (χ : ClassFunction G ℂ))
      (fun a _ b _ h => heinj h)]
  have step₂ : (∑ χ ∈ T, (f₂ χ : ℂ) • (χ : ClassFunction G ℂ))
      = ∑ k : Fin 4, ((![1, -1, 1, -1] : Fin 4 → ℤ) k : ℂ) • χk k := by
    have key : ∀ χ ∈ T, (f₂ χ : ℂ) • (χ : ClassFunction G ℂ)
        = ((f₂ χ * f₁ χ : ℤ) : ℂ) • ((f₁ χ : ℂ) • (χ : ClassFunction G ℂ)) := by
      intro χ hχ
      rw [hsmul]
      congr 1
      rw [show (f₂ χ * f₁ χ) * f₁ χ = f₂ χ by rw [mul_assoc, hf₁sq χ hχ, mul_one]]
    rw [Finset.sum_congr rfl key, hTimg,
      Finset.sum_image (s := Finset.univ) (g := e)
        (f := fun χ : IrreducibleCharacter G =>
          ((f₂ χ * f₁ χ : ℤ) : ℂ) • ((f₁ χ : ℂ) • (χ : ClassFunction G ℂ)))
        (fun a _ b _ h => heinj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [hb k]
  have step₃ : (∑ χ ∈ T, (f₃ χ : ℂ) • (χ : ClassFunction G ℂ))
      = ∑ k : Fin 4, ((![1, 1, -1, -1] : Fin 4 → ℤ) k : ℂ) • χk k := by
    have key : ∀ χ ∈ T, (f₃ χ : ℂ) • (χ : ClassFunction G ℂ)
        = ((f₃ χ * f₁ χ : ℤ) : ℂ) • ((f₁ χ : ℂ) • (χ : ClassFunction G ℂ)) := by
      intro χ hχ
      rw [hsmul]
      congr 1
      rw [show (f₃ χ * f₁ χ) * f₁ χ = f₃ χ by rw [mul_assoc, hf₁sq χ hχ, mul_one]]
    rw [Finset.sum_congr rfl key, hTimg,
      Finset.sum_image (s := Finset.univ) (g := e)
        (f := fun χ : IrreducibleCharacter G =>
          ((f₃ χ * f₁ χ : ℤ) : ℂ) • ((f₁ χ : ℂ) • (χ : ClassFunction G ℂ)))
        (fun a _ b _ h => heinj h)]
    exact Finset.sum_congr rfl fun k _ => by rw [hc k]
  refine ⟨χk 0, χk 1, χk 2, χk 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isPmIrr_zsmul_of_sq_eq_one (e 0).isIrreducible (sq_eq_one_iff.mp (hsq (e 0) (heT 0)).1)
  · exact isPmIrr_zsmul_of_sq_eq_one (e 1).isIrreducible (sq_eq_one_iff.mp (hsq (e 1) (heT 1)).1)
  · exact isPmIrr_zsmul_of_sq_eq_one (e 2).isIrreducible (sq_eq_one_iff.mp (hsq (e 2) (heT 2)).1)
  · exact isPmIrr_zsmul_of_sq_eq_one (e 3).isIrreducible (sq_eq_one_iff.mp (hsq (e 3) (heT 3)).1)
  · rw [h₁, step₁, Fin.sum_univ_four]
  · rw [h₂, step₂, Fin.sum_univ_four]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
    abel
  · rw [h₃, step₃, Fin.sum_univ_four]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three]
    abel




/-- `𝒮'(χ)` is finite (it is a set of irreducible characters of a finite group). -/
theorem caseA_bset'_finite {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) (χ : ClassFunction G ℂ) :
    (bset' C β₂ χ).Finite := by
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  refine (Set.finite_univ.image
    (fun ν : IrreducibleCharacter ↥C.P.H0 => (ν : ClassFunction ↥C.P.H0 ℂ))).subset ?_
  intro ν hν
  exact ⟨⟨ν, hν.1.1⟩, Set.mem_univ _, rfl⟩

/-- **BG Lemma 4.1 (i), the bound `|𝒮'(χ)| ≤ 3`** — proved from the clean inputs `l41_iff`
(`𝒮'(χ) ∋ ν ↔ 𝒮(χ) ∩ Λν ≠ ∅` for `ν ∈ 𝒮₄(C)`), Theorem 3.2 (`|𝒮(χ)| ≤ 3`, `thm32`) and the
finiteness of `𝒮(χ)` (`s02_bset_finite`), by exhibiting an injection `𝒮'(χ) → 𝒮(χ)`:
`ν ↦` any element of `𝒮(χ) ∩ Λν`.  (This is the only part of BG Lemma 4.1 that the proof of
Theorem 4.3 case (a) uses; it needs neither Lemma 3.3 nor Lemma 3.4.) -/
theorem caseA_bset'_ncard_le_three {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hc : Compat D C) (hn : D.n = 2) (β₂ : quotGroup C.P →* ℂˣ) (hβ : β₂ ≠ 1)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (_hne : (bset' C β₂ χ).Nonempty) :
    (bset' C β₂ χ).ncard ≤ 3 := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥C.P.H0) := finite_irreducibleCharacter
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite _
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hc hn
  obtain ⟨f, hf⟩ := Work.BG.CaseACopy.l41_isCoherent_exists D C hc hn hβ
  have hiff := Work.BG.CaseACopy.l41_iff D C hc hn β₂ hβ f hf χ hχ
  have hle3 : (bset C f χ).ncard ≤ 3 := thm32 D C hc (l41_sec3Hyp D hn) f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  -- a choice function picking a member of `𝒮(χ) ∩ Λν`
  set g : ClassFunction ↥C.P.H0 ℂ → ClassFunction ↥C.P.H0 ℂ := fun ν =>
    if h : (bset C f χ ∩ lamOrbit C ν).Nonempty then Classical.choose h else ν with hgdef
  have hg_spec : ∀ ν (h : (bset C f χ ∩ lamOrbit C ν).Nonempty),
      g ν ∈ bset C f χ ∩ lamOrbit C ν := by
    intro ν h
    rw [hgdef]
    simp only [dif_pos h]
    exact Classical.choose_spec h
  -- the map `ν ↦ g ν` is injective on `𝒮'(χ)`
  have hginj : Set.InjOn (fun ν => g ν) (bset' C β₂ χ) := by
    intro ν hν ν' hν' heq
    have heq' : g ν = g ν' := heq
    have hb : (bset C f χ ∩ lamOrbit C ν).Nonempty := (hiff ν hν.1).mp hν
    have hb' : (bset C f χ ∩ lamOrbit C ν').Nonempty := (hiff ν' hν'.1).mp hν'
    have h1 : g ν ∈ lamOrbit C ν := (hg_spec ν hb).2
    have h2' : g ν' ∈ lamOrbit C ν' := (hg_spec ν' hb').2
    rw [heq'] at h1
    rw [lamOrbit_eq C h2 hβ ν] at h1
    rw [lamOrbit_eq C h2 hβ ν'] at h2'
    simp only [Set.mem_ofPred_eq] at h1 h2'
    rcases h1 with h1 | h1 <;> rcases h2' with h2'' | h2''
    · exact h1.symm.trans h2''
    · exfalso
      have hcon : ν = lamCF C β₂ * ν' := h1.symm.trans h2''
      rw [hcon] at hν
      exact caseA_lam_two_notMem_S4Index C h2 hβ hν'.1 hν.1
    · exfalso
      have hcon : ν' = lamCF C β₂ * ν := h2''.symm.trans h1
      rw [hcon] at hν'
      exact caseA_lam_two_notMem_S4Index C h2 hβ hν.1 hν'.1
    · have hlam : lamCF C β₂ * ν = lamCF C β₂ * ν' := h1.symm.trans h2''
      have hmul : ∀ φ : ClassFunction ↥C.P.H0 ℂ, lamCF C β₂ * (lamCF C β₂ * φ) = φ := by
        intro φ
        rw [← mul_assoc_cf, lamCF_two_mul_self C h2, one_mul_cf]
      rw [← hmul ν, ← hmul ν', hlam]
  exact le_trans (Set.ncard_le_ncard_of_injOn (fun ν => g ν)
    (fun ν hν => (hg_spec ν ((hiff ν hν.1).mp hν)).1) hginj hfin) hle3

/-- The cardinality clause of BG Lemma 4.1 (i): for `χ ∈ ±Irr(G)` with `𝒮'(χ) ≠ ∅`,
`|𝒮'(χ)| ∈ {1,3}`.  This is deduced from the shape lemma `l41Shape` (`caseA_l41Shape`), which
needs a coherent map `f` (`l41_isCoherent_exists`). -/
theorem caseA_lemma41i_aux {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ}
    (hShape : ∀ (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ), IsCoherent C f →
      ∀ χ : ClassFunction G ℂ, IsPmIrr χ → (bset' C β₂ χ).Nonempty →
      ((bset C f χ).ncard = 1 ∨ (bset C f χ).ncard = 3) ∧
      (bset' C β₂ χ).ncard = (bset C f χ).ncard)
    (hc : Compat D C) (hn : D.n = 2) (hβ : β₂ ≠ 1)
    {χ : ClassFunction G ℂ} (hχ : IsPmIrr χ) (hne : (bset' C β₂ χ).Nonempty) :
    (bset' C β₂ χ).ncard = 1 ∨ (bset' C β₂ χ).ncard = 3 := by
  obtain ⟨f, hf⟩ := Work.BG.CaseACopy.l41_isCoherent_exists D C hc hn hβ
  obtain ⟨h1, h2⟩ := hShape f hf χ hχ hne
  rw [h2]
  exact h1

/-- `ConjBy` is symmetric: `ConjBy` is quantified over pairs of elements of `B` only, so no
hypothesis on the conjugating element is needed. -/
theorem caseA_conjBy_symm (D : BGData G) {x : G} {θ θ' : ClassFunction ↥D.B ℂ}
    (h : ConjBy D x θ θ') : ConjBy D x⁻¹ θ' θ := by
  intro b b' hb'
  exact (h b' b (by rw [hb']; group)).symm

/-- `NSConj` is reflexive. -/
theorem caseA_NSConj_refl (D : BGData G) (θ : ClassFunction ↥D.B ℂ) : NSConj D θ θ := by
  refine ⟨1, Subgroup.one_mem _, fun b b' hb' => ?_⟩
  have h : b' = b := Subtype.ext (by simpa using hb')
  rw [h]

/-- `NSConj` is symmetric. -/
theorem caseA_NSConj_symm (D : BGData G) {θ θ' : ClassFunction ↥D.B ℂ}
    (h : NSConj D θ θ') : NSConj D θ' θ := by
  obtain ⟨x, hxN, hx⟩ := h
  exact ⟨x⁻¹, Subgroup.inv_mem _ hxN, caseA_conjBy_symm D hx⟩

/-- `NSConj` is transitive, given that `N_G(S)` normalises `B`. -/
theorem caseA_NSConj_trans (D : BGData G)
    (hNB : ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    {θ θ' θ'' : ClassFunction ↥D.B ℂ} (h : NSConj D θ θ') (h' : NSConj D θ' θ'') :
    NSConj D θ θ'' := by
  obtain ⟨x, hxN, hx⟩ := h
  obtain ⟨y, hyN, hy⟩ := h'
  have hyxN : y * x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hyN hxN
  refine ⟨y * x, hyxN, ?_⟩
  have h1 : θ' = conjCF D x (hNB x hxN) θ := eq_conjCF_of_conjBy D x (hNB x hxN) θ hx
  have h2 : θ'' = conjCF D y (hNB y hyN) θ' := eq_conjCF_of_conjBy D y (hNB y hyN) θ' hy
  rw [h2, h1, conjCF_comp D x y (hNB y hyN) (hNB x hxN) (hNB (y * x) hyxN) θ]
  exact conjBy_conjCF D (y * x) (hNB (y * x) hyxN) θ

/-- Integer coefficient of the irreducible `χ` in the expansion of `δ_ν` over the four-element
set `T`. -/
noncomputable def caseACoeff (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (β₂ : quotGroup C.P →* ℂˣ) (T : Finset (IrreducibleCharacter G))
    (ν : ClassFunction ↥C.P.H0 ℂ) (χ : IrreducibleCharacter G) : ℤ :=
  if χ ∈ T then
    (if ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 1 then 1 else -1)
  else 0

theorem caseACoeff_cast (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} {T : Finset (IrreducibleCharacter G)}
    {ν : ClassFunction ↥C.P.H0 ℂ} {χ : IrreducibleCharacter G} (hχ : χ ∈ T)
    (h : ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 1 ∨
      ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = -1) :
    (caseACoeff C β₂ T ν χ : ℂ) = ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) := by
  classical
  rcases h with h | h
  · rw [caseACoeff, if_pos hχ, if_pos h, h]; norm_num
  · rw [caseACoeff, if_pos hχ, if_neg (by rw [h]; norm_num), h]; norm_num

theorem caseACoeff_sq (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} {T : Finset (IrreducibleCharacter G)}
    {ν : ClassFunction ↥C.P.H0 ℂ} {χ : IrreducibleCharacter G} (hχ : χ ∈ T)
    (h : ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 1 ∨
      ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = -1) :
    caseACoeff C β₂ T ν χ ^ 2 = 1 := by
  classical
  classical
  rcases h with h | h
  · rw [caseACoeff, if_pos hχ, if_pos h]; norm_num
  · rw [caseACoeff, if_pos hχ, if_neg (by rw [h]; norm_num)]; norm_num

/-- Expansion of `δ_ν` over the support `T`. -/
theorem caseACoeff_expansion (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} {T : Finset (IrreducibleCharacter G)}
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hZ : delta C β₂ ν ∈ ZIrr G)
    (hiff : ∀ χ : IrreducibleCharacter G,
      χ ∈ T ↔ ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) ≠ 0)
    (hval : ∀ χ ∈ T, ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = 1 ∨
      ClassFunction.inner (delta C β₂ ν) (χ : ClassFunction G ℂ) = -1) :
    delta C β₂ ν = ∑ χ ∈ T, (caseACoeff C β₂ T ν χ : ℂ) • (χ : ClassFunction G ℂ) := by
  classical
  rw [caseA_eq_sum_of_support hZ T hiff]
  exact Finset.sum_congr rfl fun χ hχ => by
    rw [← caseACoeff_cast C hχ (hval χ hχ)]

/-- Orthogonality of two coefficient vectors, from the orthogonality of the corresponding
virtual characters. -/
theorem caseACoeff_orth (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {β₂ : quotGroup C.P →* ℂˣ} {T : Finset (IrreducibleCharacter G)}
    {ν ν' : ClassFunction ↥C.P.H0 ℂ} {δ δ' : ClassFunction G ℂ}
    (hδ : δ = ∑ χ ∈ T, (caseACoeff C β₂ T ν χ : ℂ) • (χ : ClassFunction G ℂ))
    (hδ' : δ' = ∑ χ ∈ T, (caseACoeff C β₂ T ν' χ : ℂ) • (χ : ClassFunction G ℂ))
    (horth : ClassFunction.inner δ δ' = 0) :
    ∑ χ ∈ T, caseACoeff C β₂ T ν χ * caseACoeff C β₂ T ν' χ = 0 := by
  classical
  have h := caseA_inner_eq_sum_coeff T (caseACoeff C β₂ T ν) (caseACoeff C β₂ T ν') hδ hδ'
  have hcast : ((∑ χ ∈ T, caseACoeff C β₂ T ν χ * caseACoeff C β₂ T ν' χ : ℤ) : ℂ) = 0 := by
    rw [← h]; exact horth
  exact (Int.cast_eq_zero).mp hcast


open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
/-- **BG Theorem 4.3, case (a)**: if `μ ∈ 𝒮₄(C)` has a hat which is not fixed by `N_G(S)`, then
every `ν` in the component of `μ` in `Δ` satisfies the triple pattern (`TripleAt`). -/
theorem caseA_main {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hNB : ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B)
    (hNOrb : NOrbProp D)
    (hNcard : ∀ (β₂ : quotGroup C.P →* ℂˣ), β₂ ≠ 1 → ∀ χ : ClassFunction G ℂ, IsPmIrr χ →
      (bset' C β₂ χ).Nonempty → (bset' C β₂ χ).ncard ≤ 3) :
    Work.GW2.C23.CaseAProp D C := by
  classical
  intro hc hn β₂ hβ μ hμ θ hθ hnf ν hconn
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- ### the leaf statements
  have hHat : HatProp D C := Hat D C
  have hInj : HatInjProp D C := hatInj D C
  have hL41v : L41vProp D C := l41v D C
  have hDS : DeltaShapeProp D C := deltaShape D C
  -- ### the `N_G(S)`-orbit of the hat `θ`
  obtain ⟨θ₂, θ₃, hconj₂, hconj₃, hθθ₂, hθθ₃, hθ₂θ₃, _hclass⟩ := hNOrb hn θ hnf
  -- ### the support of `δ_μ`
  obtain ⟨T, hTcard, hTsign, hTzero⟩ := hDS hc hn β₂ hβ μ hμ
  have hTiff : ∀ χ : IrreducibleCharacter G,
      χ ∈ T ↔ ClassFunction.inner (delta C β₂ μ) (χ : ClassFunction G ℂ) ≠ 0 := by
    intro χ
    constructor
    · intro hχ
      rcases hTsign χ hχ with h | h <;> rw [h] <;> norm_num
    · intro hne
      by_contra hnot
      exact hne (hTzero χ hnot)
  have hmem_mu : ∀ χ : IrreducibleCharacter G, χ ∈ T →
      μ ∈ bset' C β₂ (χ : ClassFunction G ℂ) := by
    intro χ hχ
    refine ⟨hμ, ?_⟩
    rw [ClassFunction.inner_star_comm]
    exact star_ne_zero.mpr ((hTiff χ).mp hχ)
  -- ### the other two members of the triple
  obtain ⟨χ₀, hχ₀T⟩ := Finset.card_pos.mp (by rw [hTcard]; norm_num)
  obtain ⟨x₂, hx₂N, hcx₂⟩ := hconj₂
  obtain ⟨x₃, hx₃N, hcx₃⟩ := hconj₃
  obtain ⟨μ₂, hμ₂bset, hμ₂hat⟩ :=
    hL41v hc hn β₂ hβ (χ₀ : ClassFunction G ℂ) (Or.inl χ₀.isIrreducible)
      μ (hmem_mu χ₀ hχ₀T) θ hθ x₂ hx₂N θ₂ hcx₂
  obtain ⟨μ₃, hμ₃bset, hμ₃hat⟩ :=
    hL41v hc hn β₂ hβ (χ₀ : ClassFunction G ℂ) (Or.inl χ₀.isIrreducible)
      μ (hmem_mu χ₀ hχ₀T) θ hθ x₃ hx₃N θ₃ hcx₃
  have hμ₂S : μ₂ ∈ S4Index C := hμ₂bset.1
  have hμ₃S : μ₃ ∈ S4Index C := hμ₃bset.1
  have hμμ₂ : μ ≠ μ₂ := by
    intro h
    refine hθθ₂ ((hHat hc hn μ hμ).2 θ θ₂ hθ ?_)
    rw [h]; exact hμ₂hat
  have hμμ₃ : μ ≠ μ₃ := by
    intro h
    refine hθθ₃ ((hHat hc hn μ hμ).2 θ θ₃ hθ ?_)
    rw [h]; exact hμ₃hat
  have hμ₂μ₃ : μ₂ ≠ μ₃ := by
    intro h
    refine hθ₂θ₃ ((hHat hc hn μ₂ hμ₂S).2 θ₂ θ₃ hμ₂hat ?_)
    rw [h]; exact hμ₃hat
  -- ### the two further members of `𝒮'(χ)`
  have hmem_mu₂ : ∀ χ : IrreducibleCharacter G, χ ∈ T →
      μ₂ ∈ bset' C β₂ (χ : ClassFunction G ℂ) := by
    intro χ hχ
    obtain ⟨m, hmbset, hmhat⟩ :=
      hL41v hc hn β₂ hβ (χ : ClassFunction G ℂ) (Or.inl χ.isIrreducible)
        μ (hmem_mu χ hχ) θ hθ x₂ hx₂N θ₂ hcx₂
    have heq : m = μ₂ := hInj hc hn m hmbset.1 μ₂ hμ₂S θ₂ hmhat hμ₂hat
    rwa [heq] at hmbset
  have hmem_mu₃ : ∀ χ : IrreducibleCharacter G, χ ∈ T →
      μ₃ ∈ bset' C β₂ (χ : ClassFunction G ℂ) := by
    intro χ hχ
    obtain ⟨m, hmbset, hmhat⟩ :=
      hL41v hc hn β₂ hβ (χ : ClassFunction G ℂ) (Or.inl χ.isIrreducible)
        μ (hmem_mu χ hχ) θ hθ x₃ hx₃N θ₃ hcx₃
    have heq : m = μ₃ := hInj hc hn m hmbset.1 μ₃ hμ₃S θ₃ hmhat hμ₃hat
    rwa [heq] at hmbset
  have hmem_triple : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ : IrreducibleCharacter G, χ ∈ T → ν' ∈ bset' C β₂ (χ : ClassFunction G ℂ) := by
    intro ν' hν' χ hχ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν'
    rcases hν' with rfl | rfl | rfl
    · exact hmem_mu χ hχ
    · exact hmem_mu₂ χ hχ
    · exact hmem_mu₃ χ hχ
  have hS4_triple : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)), ν' ∈ S4Index C := by
    intro ν' hν'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hν'
    rcases hν' with rfl | rfl | rfl
    · exact hμ
    · exact hμ₂S
    · exact hμ₃S
  have htriple_ncard : ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨μ, μ₂, μ₃, hμμ₂, hμμ₃, hμ₂μ₃, rfl⟩
  -- ### `𝒮'(χ) = {μ, μ₂, μ₃}` for `χ ∈ T`
  have hbset_eq : ∀ χ : IrreducibleCharacter G, χ ∈ T →
      bset' C β₂ (χ : ClassFunction G ℂ) = {μ, μ₂, μ₃} := by
    intro χ hχ
    have hsub : ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆
        bset' C β₂ (χ : ClassFunction G ℂ) := fun x hx => hmem_triple x hx χ hχ
    have hcard := hNcard β₂ hβ (χ : ClassFunction G ℂ)
      (Or.inl χ.isIrreducible) ⟨μ, hmem_mu χ hχ⟩
    have hfinS : (bset' C β₂ (χ : ClassFunction G ℂ)).Finite :=
      caseA_bset'_finite C β₂ (χ : ClassFunction G ℂ)
    have h3 : (bset' C β₂ (χ : ClassFunction G ℂ)).ncard = 3 := by
      have hle : ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard ≤
          (bset' C β₂ (χ : ClassFunction G ℂ)).ncard := Set.ncard_le_ncard hsub hfinS
      rw [htriple_ncard] at hle
      omega
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [h3, htriple_ncard])
      (Set.finite_of_ncard_ne_zero (by rw [h3]; norm_num))).symm
  -- ### the shape of `δ_ν` relative to `T` for all three members
  have hshape : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      delta C β₂ ν' ∈ ZIrr G ∧
      (∀ χ ∈ T, ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) = 1 ∨
        ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) = -1) ∧
      (∀ χ : IrreducibleCharacter G, χ ∉ T →
        ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) = 0) := by
    intro ν' hν'
    obtain ⟨T', hT'card, hT'sign, hT'zero⟩ := hDS hc hn β₂ hβ ν' (hS4_triple ν' hν')
    have hsub' : T ⊆ T' := by
      intro χ hχ
      by_contra hnot
      have h1 := hT'zero χ hnot
      have h2 : ClassFunction.inner (χ : ClassFunction G ℂ) (delta C β₂ ν') ≠ 0 :=
        (hmem_triple ν' hν' χ hχ).2
      rw [ClassFunction.inner_star_comm] at h2
      exact h2 (by rw [h1]; simp)
    have hTeq : T = T' := Finset.eq_of_subset_of_card_le (s := T) (t := T') hsub'
      (by rw [hT'card, hTcard])
    exact ⟨l41_delta_mem_ZIrr C (hS4_triple ν' hν').1, fun χ hχ => hT'sign χ (hsub' hχ),
      fun χ hχ => hT'zero χ (by simpa [← hTeq] using hχ)⟩
  have hsupp_iff : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ : IrreducibleCharacter G,
      χ ∈ T ↔ ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) ≠ 0 := by
    intro ν' hν' χ
    constructor
    · intro hχ
      rcases (hshape ν' hν').2.1 χ hχ with h | h <;> rw [h] <;> norm_num
    · intro hne
      by_contra hnot
      exact hne ((hshape ν' hν').2.2 χ hnot)
  -- ### the integer coefficient vectors
  have hcf_cast : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ ∈ T, (caseACoeff C β₂ T ν' χ : ℂ) =
        ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) :=
    fun ν' hν' χ hχ => caseACoeff_cast C hχ ((hshape ν' hν').2.1 χ hχ)
  have hcf_sq : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ ∈ T, caseACoeff C β₂ T ν' χ ^ 2 = 1 :=
    fun ν' hν' χ hχ => caseACoeff_sq C hχ ((hshape ν' hν').2.1 χ hχ)
  have hcf_exp : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      delta C β₂ ν' = ∑ χ ∈ T, (caseACoeff C β₂ T ν' χ : ℂ) • (χ : ClassFunction G ℂ) :=
    fun ν' hν' => caseACoeff_expansion C (hshape ν' hν').1 (hsupp_iff ν' hν')
      ((hshape ν' hν').2.1)
  have hcf_orth : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ ν'' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)), ν' ≠ ν'' →
      ∑ χ ∈ T, caseACoeff C β₂ T ν' χ * caseACoeff C β₂ T ν'' χ = 0 := by
    intro ν' hν' ν'' hν'' hne
    have h := caseA_delta_orth (D := D) (C := C) hc hn (β₂ := β₂) hβ
      (ν := ν'') (μ := ν') (hS4_triple ν'' hν'') (hS4_triple ν' hν') hne
    have h' : ClassFunction.inner (delta C β₂ ν') (delta C β₂ ν'') = 0 := by
      rw [ClassFunction.inner_star_comm, h, star_zero]
    exact caseACoeff_orth C (hcf_exp ν' hν') (hcf_exp ν'' hν'') h'
  -- ### every element adjacent to a member of the triple is in the triple
  have hadj_mem : ∀ b ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ ν', Adj C β₂ b ν' → ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    intro b hb ν' hadj
    obtain ⟨-, hν'S4, -, hnd⟩ := hadj
    have hnd' : ∃ χ : IrreducibleCharacter G,
        ClassFunction.inner (delta C β₂ b) (χ : ClassFunction G ℂ) ≠ 0 ∧
        ClassFunction.inner (delta C β₂ ν') (χ : ClassFunction G ℂ) ≠ 0 := by
      by_contra hcon
      apply hnd
      intro χ
      by_cases h1 : ClassFunction.inner (delta C β₂ b) (χ : ClassFunction G ℂ) = 0
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        exact hcon ⟨χ, h1, h2⟩
    obtain ⟨χ, hbχ, hν'χ⟩ := hnd'
    have hχT : χ ∈ T := (hsupp_iff b hb χ).mpr hbχ
    have hν'trp : ν' ∈ bset' C β₂ (χ : ClassFunction G ℂ) := by
      refine ⟨hν'S4, ?_⟩
      rw [ClassFunction.inner_star_comm]
      exact star_ne_zero.mpr hν'χ
    rwa [hbset_eq χ hχT] at hν'trp
  have hconn_sub : ∀ ν' : ClassFunction ↥C.P.H0 ℂ, Conn C β₂ μ ν' →
      ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    intro ν' h
    induction h with
    | refl => simp
    | tail _ hbc ih => exact hadj_mem _ ih _ hbc
  have hνtrp : ν ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := hconn_sub ν hconn
  -- ### hats of the triple are pairwise `N_G(S)`-conjugate
  have hm₁ : μ ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by simp
  have hm₂ : μ₂ ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by simp
  have hm₃ : μ₃ ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)) := by simp
  have hhat_mem : ∀ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ θ', HatOf D C ν' θ' → NSConj D θ θ' := by
    intro ν' hν' θ' hθ'
    have key : ν' = μ ∨ ν' = μ₂ ∨ ν' = μ₃ → NSConj D θ θ' := by
      rintro (h | h | h)
      · rw [h] at hθ'
        rw [(hHat hc hn μ hμ).2 θ' θ hθ' hθ]
        exact caseA_NSConj_refl D θ
      · rw [h] at hθ'
        rw [(hHat hc hn μ₂ hμ₂S).2 θ' θ₂ hθ' hμ₂hat]
        exact ⟨x₂, hx₂N, hcx₂⟩
      · rw [h] at hθ'
        rw [(hHat hc hn μ₃ hμ₃S).2 θ' θ₃ hθ' hμ₃hat]
        exact ⟨x₃, hx₃N, hcx₃⟩
    exact key (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hν')
  have hhat_conj : ∀ θ' θ'', (∃ ν' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)),
        HatOf D C ν' θ') →
      (∃ ν'' ∈ ({μ, μ₂, μ₃} : Set (ClassFunction ↥C.P.H0 ℂ)), HatOf D C ν'' θ'') →
      NSConj D θ' θ'' := by
    intro θ' θ'' h1 h2
    obtain ⟨ν', hν', hh1⟩ := h1
    obtain ⟨ν'', hν'', hh2⟩ := h2
    exact caseA_NSConj_trans D hNB (caseA_NSConj_symm D (hhat_mem ν' hν' θ' hh1))
      (hhat_mem ν'' hν'' θ'' hh2)
  -- ### the three cases of the base point
  have hTA : ∀ a : ClassFunction ↥C.P.H0 ℂ, a = μ ∨ a = μ₂ ∨ a = μ₃ → TripleAt D C β₂ a := by
    rintro a (h | h | h)
    · rw [h]
      obtain ⟨χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃⟩ :=
        caseA_hadamard_triple hTcard (caseACoeff C β₂ T μ) (caseACoeff C β₂ T μ₂)
          (caseACoeff C β₂ T μ₃) (delta C β₂ μ) (delta C β₂ μ₂) (delta C β₂ μ₃)
          (fun χ hχ => ⟨hcf_sq μ hm₁ χ hχ, hcf_sq μ₂ hm₂ χ hχ, hcf_sq μ₃ hm₃ χ hχ⟩)
          (hcf_exp μ hm₁) (hcf_exp μ₂ hm₂) (hcf_exp μ₃ hm₃)
          (hcf_orth μ hm₁ μ₂ hm₂ hμμ₂) (hcf_orth μ hm₁ μ₃ hm₃ hμμ₃)
          (hcf_orth μ₂ hm₂ μ₃ hm₃ hμ₂μ₃)
      refine ⟨μ₂, hμ₂S, μ₃, hμ₃S, χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃, ?_⟩
      intro θ' hθ'
      exact ⟨⟨θ₂, hμ₂hat, hhat_conj θ' θ₂ ⟨μ, hm₁, hθ'⟩ ⟨μ₂, hm₂, hμ₂hat⟩⟩,
        ⟨θ₃, hμ₃hat, hhat_conj θ' θ₃ ⟨μ, hm₁, hθ'⟩ ⟨μ₃, hm₃, hμ₃hat⟩⟩⟩
    · rw [h]
      obtain ⟨χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃⟩ :=
        caseA_hadamard_triple hTcard (caseACoeff C β₂ T μ₂) (caseACoeff C β₂ T μ)
          (caseACoeff C β₂ T μ₃) (delta C β₂ μ₂) (delta C β₂ μ) (delta C β₂ μ₃)
          (fun χ hχ => ⟨hcf_sq μ₂ hm₂ χ hχ, hcf_sq μ hm₁ χ hχ, hcf_sq μ₃ hm₃ χ hχ⟩)
          (hcf_exp μ₂ hm₂) (hcf_exp μ hm₁) (hcf_exp μ₃ hm₃)
          (hcf_orth μ₂ hm₂ μ hm₁ hμμ₂.symm) (hcf_orth μ₂ hm₂ μ₃ hm₃ hμ₂μ₃)
          (hcf_orth μ hm₁ μ₃ hm₃ hμμ₃)
      refine ⟨μ, hμ, μ₃, hμ₃S, χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃, ?_⟩
      intro θ' hθ'
      exact ⟨⟨θ, hθ, hhat_conj θ' θ ⟨μ₂, hm₂, hθ'⟩ ⟨μ, hm₁, hθ⟩⟩,
        ⟨θ₃, hμ₃hat, hhat_conj θ' θ₃ ⟨μ₂, hm₂, hθ'⟩ ⟨μ₃, hm₃, hμ₃hat⟩⟩⟩
    · rw [h]
      obtain ⟨χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃⟩ :=
        caseA_hadamard_triple hTcard (caseACoeff C β₂ T μ₃) (caseACoeff C β₂ T μ)
          (caseACoeff C β₂ T μ₂) (delta C β₂ μ₃) (delta C β₂ μ) (delta C β₂ μ₂)
          (fun χ hχ => ⟨hcf_sq μ₃ hm₃ χ hχ, hcf_sq μ hm₁ χ hχ, hcf_sq μ₂ hm₂ χ hχ⟩)
          (hcf_exp μ₃ hm₃) (hcf_exp μ hm₁) (hcf_exp μ₂ hm₂)
          (hcf_orth μ₃ hm₃ μ hm₁ hμμ₃.symm) (hcf_orth μ₃ hm₃ μ₂ hm₂ hμ₂μ₃.symm)
          (hcf_orth μ hm₁ μ₂ hm₂ hμμ₂)
      refine ⟨μ, hμ, μ₂, hμ₂S, χ₁, χ₂, χ₃, χ₄, hp₁, hp₂, hp₃, hp₄, he₁, he₂, he₃, ?_⟩
      intro θ' hθ'
      exact ⟨⟨θ, hθ, hhat_conj θ' θ ⟨μ₃, hm₃, hθ'⟩ ⟨μ, hm₁, hθ⟩⟩,
        ⟨θ₂, hμ₂hat, hhat_conj θ' θ₂ ⟨μ₃, hm₃, hθ'⟩ ⟨μ₂, hm₂, hμ₂hat⟩⟩⟩
  exact hTA ν (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hνtrp)

/-- `NOrbProp` from the group-theoretic inputs (`caseA_nOrbGroup`) and the
`N_G(S)`-invariance of `B` (`Work.BG.l41vBInv`). -/
theorem caseA_NOrbProp {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (hn : D.n = 2)
    (hG : (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) ∧
      (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
      (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
        ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
          y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2))) :
    NOrbProp D := by
  intro _hn θ hnf
  have hBinv_raw : ∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B := l41vBInv D hn
  have hbInv : (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      ∀ b ∈ D.B, x⁻¹ * b * x ∈ D.B) ∧
      (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) := ⟨hBinv_raw, hG.1⟩
  have hcos : (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
      (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
        ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
          y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2)) :=
    ⟨hG.2.1, hG.2.2⟩
  obtain ⟨hBinv, hInner⟩ := hbInv
  obtain ⟨hCube, hCover⟩ := hcos
  set C : Subgroup G := Subgroup.centralizer ((D.S : Subgroup G) : Set G) with hCdef
  set N : Subgroup G := Subgroup.normalizer ((D.S : Subgroup G) : Set G) with hNdef
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer ((D.S : Subgroup G) : Set G)
  -- (1) an element `x ∈ N` at which `θ` is not fixed
  have hnf' : ∃ x ∈ N, ¬ ConjBy D x θ θ := by
    by_contra h
    refine hnf fun x hx => ?_
    by_contra hconj
    exact h ⟨x, hx, hconj⟩
  obtain ⟨x, hxN, hxnot⟩ := hnf'
  -- (2) elements of `C` act trivially on class functions of `B`
  have hfixC : ∀ (c : G) (hc : c ∈ C) (hcN : c ∈ N) (φ : ClassFunction ↥D.B ℂ),
      conjCF D c (hBinv c hcN) φ = φ := by
    intro c hc hcN φ
    ext b
    simp only [conjCF_apply]
    obtain ⟨b₀, hb₀, hconj⟩ := hInner c hc b b.2
    have hE : (⟨c⁻¹ * (b : G) * c, hBinv c hcN b b.2⟩ : ↥D.B) =
        (⟨b₀, hb₀⟩ : ↥D.B) * b * ((⟨b₀, hb₀⟩ : ↥D.B))⁻¹ :=
      Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj)
    rw [hE]
    exact φ.conj_eq b ⟨b₀, hb₀⟩
  have hxnotC : x ∉ C := by
    intro hxC
    refine hxnot ?_
    have h := conjBy_conjCF D x (hBinv x hxN) θ
    rwa [hfixC x hxC hxN θ] at h
  -- (3) the three conjugates
  have hxxN : x * x ∈ N := N.mul_mem hxN hxN
  have hxxxN : x * (x * x) ∈ N := N.mul_mem hxN hxxN
  have hcomp : ∀ (y z : G) (hy : y ∈ N) (hz : z ∈ N) (φ : ClassFunction ↥D.B ℂ),
      conjCF D y (hBinv y hy) (conjCF D z (hBinv z hz) φ)
        = conjCF D (y * z) (hBinv (y * z) (N.mul_mem hy hz)) φ :=
    fun y z hy hz φ =>
      conjCF_comp D z y (hBinv y hy) (hBinv z hz) (hBinv (y * z) (N.mul_mem hy hz)) φ
  have hx3eq : x ^ 3 = x * (x * x) := by
    show x ^ (2 + 1) = x * (x * x)
    rw [pow_succ', pow_two]
  have hx3C : x * (x * x) ∈ C := by
    have h := hCube x hxN
    rwa [hx3eq] at h
  have hcube : conjCF D (x * (x * x)) (hBinv (x * (x * x)) hxxxN) θ = θ :=
    hfixC (x * (x * x)) hx3C hxxxN θ
  have hθx : conjCF D x (hBinv x hxN) θ ≠ θ := by
    intro h
    refine hxnot ?_
    have hh := conjBy_conjCF D x (hBinv x hxN) θ
    rwa [h] at hh
  have hθxx : conjCF D (x * x) (hBinv (x * x) hxxN) θ ≠ θ := by
    intro h
    have hA : conjCF D x (hBinv x hxN) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)
        = conjCF D x (hBinv x hxN) θ := by rw [h]
    rw [hcomp x (x * x) hxN hxxN θ] at hA
    exact hθx (hA.symm.trans hcube)
  have hθxx' : conjCF D (x * x) (hBinv (x * x) hxxN) θ ≠ conjCF D x (hBinv x hxN) θ := by
    intro h
    have hA : conjCF D x (hBinv x hxN) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)
        = conjCF D x (hBinv x hxN) (conjCF D x (hBinv x hxN) θ) := by rw [h]
    rw [hcomp x (x * x) hxN hxxN θ, hcomp x x hxN hxN θ] at hA
    rw [hcube] at hA
    exact hθxx hA.symm
  -- (4) assembly
  refine ⟨conjCF D x (hBinv x hxN) θ, conjCF D (x * x) (hBinv (x * x) hxxN) θ,
    ⟨x, hxN, conjBy_conjCF D x (hBinv x hxN) θ⟩,
    ⟨x * x, hxxN, conjBy_conjCF D (x * x) (hBinv (x * x) hxxN) θ⟩,
    hθx.symm, hθxx.symm, hθxx'.symm, ?_⟩
  intro θ' hθ'
  obtain ⟨y, hyN, hyc⟩ := hθ'
  have hyeq : θ' = conjCF D y (hBinv y hyN) θ := eq_conjCF_of_conjBy D y (hBinv y hyN) θ hyc
  rcases hCover x hxN hxnotC y hyN with hyC | ⟨c, hc, hycx⟩ | ⟨c, hc, hycx⟩
  · exact Or.inl (hyeq.trans (hfixC y hyC hyN θ))
  · refine Or.inr (Or.inl ?_)
    refine hyeq.trans ?_
    calc conjCF D y (hBinv y hyN) θ
        = conjCF D (c * x) (hBinv (c * x) (N.mul_mem (hCN hc) hxN)) θ :=
          conjCF_congr_arg D hycx (hBinv y hyN) (hBinv (c * x) (N.mul_mem (hCN hc) hxN)) θ
      _ = conjCF D c (hBinv c (hCN hc)) (conjCF D x (hBinv x hxN) θ) :=
          (hcomp c x (hCN hc) hxN θ).symm
      _ = conjCF D x (hBinv x hxN) θ := hfixC c hc (hCN hc) (conjCF D x (hBinv x hxN) θ)
  · refine Or.inr (Or.inr ?_)
    have hyN' : c * x ^ 2 ∈ N := hycx ▸ hyN
    refine hyeq.trans ?_
    calc conjCF D y (hBinv y hyN) θ
        = conjCF D (c * x ^ 2) (hBinv (c * x ^ 2) hyN') θ :=
          conjCF_congr_arg D hycx (hBinv y hyN) (hBinv (c * x ^ 2) hyN') θ
      _ = conjCF D (c * (x * x)) (hBinv (c * (x * x)) (N.mul_mem (hCN hc) hxxN)) θ :=
          conjCF_congr_arg D (by rw [pow_two]) (hBinv (c * x ^ 2) hyN')
            (hBinv (c * (x * x)) (N.mul_mem (hCN hc) hxxN)) θ
      _ = conjCF D c (hBinv c (hCN hc)) (conjCF D (x * x) (hBinv (x * x) hxxN) θ) :=
          (hcomp c (x * x) (hCN hc) hxxN θ).symm
      _ = conjCF D (x * x) (hBinv (x * x) hxxN) θ :=
          hfixC c hc (hCN hc) (conjCF D (x * x) (hBinv (x * x) hxxN) θ)



open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem caseA {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.CaseAProp D C := by
  intro hc hn
  -- the group-theoretic inputs for `NOrbProp`: `N_G(S)` normalises `B`, acts on `B` by inner
  -- automorphisms, and `|N_G(S) : C_G(S)| ∈ {1,3}`
  have hG : (∀ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), ∀ b ∈ D.B,
        ∃ b₀ ∈ D.B, c⁻¹ * b * c = b₀ * b * b₀⁻¹) ∧
      (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
      (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
        ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
          y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
          (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2)) :=
    caseA_nOrbGroup D hn
  exact caseA_main D C (l41vBInv D hn) (caseA_NOrbProp D hn hG)
    (fun β₂ hβ χ hχ hne => caseA_bset'_ncard_le_three D C hc hn β₂ hβ χ hχ hne) hc hn

end Work.BG.thm43
