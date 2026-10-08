import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.HS.core_mul
import Submission.Work.Higman.clo_sM_props
import Submission.Work.Higman.clo_pair_props
import Submission.Work.Higman.clo_betaV_props
import Submission.Work.Higman.MSA.l8_setup

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

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Step 1: a non-trivial `ξ`-invariant abelian normal subgroup contains `Ω₁(P)` -/

/-- A non-trivial `ξ`-invariant subgroup of `Ω₁(P)` is all of `Ω₁(P)` (the `ξ`-orbit of a
non-identity involution is everything). -/
theorem eq_omega1_of_ne_bot_of_map_eq (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ omega1 P) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S) (hne : S ≠ ⊥) :
    S = omega1 P := by
  rcases invariant_subgroup_inf_omega1 h (⊤ : Subgroup P) (by simpa using hS)
    (by simpa using hSinv) with h1 | h1
  · exact absurd h1 hne
  · simpa using h1

/-- A non-trivial finite `2`-subgroup contains an involution. -/
theorem exists_involution_of_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P} (hne : A ≠ ⊥) :
    ∃ x ∈ A, x ≠ 1 ∧ x ^ 2 = 1 := by
  have hdvd : 2 ∣ Nat.card ↥A := by
    rcases (h.isPGroup.to_subgroup A).card_eq_or_dvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp h1).1
      refine hne (le_bot_iff.mp (fun x hx => ?_))
      have hx1 : (⟨x, hx⟩ : ↥A) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx1
    · exact h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : (z : ↥A) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hz]
  refine ⟨(z : P), z.2, ?_, ?_⟩
  · intro hc
    have h1 : (z : ↥A) = 1 := Subtype.ext (by simpa using hc)
    rw [h1] at hz
    exact absurd hz (by norm_num)
  · simpa [Subgroup.coe_pow] using congrArg (fun t : ↥A => (t : P)) hz2

/-- **Step 1.**  In a Suzuki 2-group a non-trivial `ξ`-invariant abelian normal subgroup `A`
contains `Ω₁(P)`. -/
theorem omega1_le_of_isXiAbelNormal_ne_bot (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hne : A ≠ ⊥) : omega1 P ≤ A := by
  have hTinv : (A ⊓ omega1 P).map (h.xi : MulAut P).toMonoidHom = A ⊓ omega1 P := by
    rw [Subgroup.map_inf A (omega1 P) (h.xi : MulAut P).toMonoidHom
      (h.xi : MulAut P).injective, hA.map_eq, map_xi_omega1 h]
  have hTne : A ⊓ omega1 P ≠ ⊥ := by
    obtain ⟨x, hxA, hx1, hx2⟩ := exists_involution_of_ne_bot h hne
    intro hbot
    have hmem : x ∈ (A ⊓ omega1 P : Subgroup P) :=
      Subgroup.mem_inf.mpr ⟨hxA, Subgroup.subset_closure (mem_sqOne.mpr hx2)⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hEq : A ⊓ omega1 P = omega1 P :=
    eq_omega1_of_ne_bot_of_map_eq h inf_le_right hTinv hTne
  rw [← hEq]
  exact inf_le_left

/-- The conclusion `∀ a ∈ A, a * a = 1` is exactly `A ≤ Ω₁(P)`. -/
theorem sq_eq_one_of_le_omega1 (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : A ≤ omega1 P) :
    ∀ a ∈ A, a * a = 1 := by
  intro a ha
  have h2 : a ^ 2 = 1 := h.mem_omega1.mp (hA ha)
  rwa [pow_two] at h2

/-- Conversely, if every element of `A` is an involution then `A ≤ Ω₁(P)`. -/
theorem le_omega1_of_sq_eq_one {A : Subgroup P} (hsq : ∀ a ∈ A, a * a = 1) :
    A ≤ omega1 P := by
  intro a ha
  exact Subgroup.subset_closure (mem_sqOne.mpr (by rw [pow_two]; exact hsq a ha))

/-! ## Step 2: the beginning of the lower central series of `C` -/

/-- **Unipotence.**  `⁅A, C⁆ ≤ A ^ (2)` for a `ξ`-invariant abelian normal subgroup `A`. -/
theorem commutator_A_C_le (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A) :
    ⁅A, C⁆ ≤ powSub A 2 := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro u _ a ha
  exact commutator_mem_powSub_two h hA u a ha

/-! ## The hard case: reduction to the algebraic core of Higman's §4 Lemma 6 -/

/-- **The hard case of Higman's Lemma 8.**  In the situation of `clo_lemma8` with `A ≠ ⊥` and
`A ^ (2) ≠ ⊥`, there is a contradiction (Higman's §4: `C ^ (2) = C' = A`, the lower central series
`C > A > A² > A⁴ > ⋯` and the non-isomorphism Lemma 6).

The two layers `V = C/A` and `W = Ω₁(P)` are elementary abelian `ξ`-groups on which `ξ` acts
transitively away from `1`; the power map `s : V → W`, the commutator pairing `B : V × V → W` and
the bracket `β : V × W → W` are constructed in `Submission/Work/Higman/clo_hard_defs.lean` and
their properties are `clo_sM_props`, `clo_pair_props`, `clo_betaV_props`; the contradiction is the
algebraic core `Work.Higman.HS.core_mul`. -/
theorem clo_hard {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A)
    (hA0 : A ≠ ⊥) (hA2 : Work.Higman.powSub A 2 ≠ ⊥) : False := by
  haveI hAn : A.Normal := hA.normal
  -- ## Step 1: `Ω₁(P) ≤ A` and the exponent data of `A`
  have hOmega : omega1 P ≤ A := omega1_le_of_isXiAbelNormal_ne_bot h hA hA0
  obtain ⟨e, he2, he1, htopA, hkey⟩ := MSA.l8_setup h hA hA0 hA2 hOmega
  have he : 1 ≤ e := by omega
  -- ## Step 2: the hypothesis package
  let S : CloH8Data h A C :=
    { hA := hA, hCn := hCn, hCinv := hCinv, hAC := hAC, hCA := hCA, hcover := hcover,
      hC2 := hC2, hCd := hCd, hAne := hA0, hOmega := hOmega, e := e, he := he, he2 := he2,
      he1 := he1, htopA := htopA, hkey := hkey }
  -- ## Step 3: the two layers are abelian of exponent two
  letI : CommGroup (↥C ⧸ (A.subgroupOf C)) :=
    { (inferInstance : Group (↥C ⧸ (A.subgroupOf C))) with mul_comm := cloQuot_comm hCd }
  letI : CommGroup ↥(omega1 P) :=
    { (inferInstance : Group ↥(omega1 P)) with
      mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  -- ## Step 4: cardinalities: both layers have `2 ^ n` elements
  obtain ⟨n, hncard⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have h1 : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 := by simpa using Nat.pow_le_pow_right (by norm_num) h1
    have h4 := h.omega1_card_ge_four
    omega
  obtain ⟨hSMinj, hSMsurj, hSM1, hSMeq, hSMpol⟩ := clo_sM_props S
  have hVcard : Nat.card (↥C ⧸ (A.subgroupOf C)) = 2 ^ n := by
    have h1 : Nat.card (↥C ⧸ (A.subgroupOf C)) ≤ Nat.card ↥(omega1 P) :=
      Nat.card_le_card_of_injective _ hSMinj
    have h2 : Nat.card ↥(omega1 P) ≤ Nat.card (↥C ⧸ (A.subgroupOf C)) :=
      Nat.card_le_card_of_surjective _ hSMsurj
    rw [le_antisymm h1 h2, hncard]
  have hWcard : Nat.card ↥(omega1 P) = 2 ^ n := hncard
  -- ## Step 5: the properties of the three maps
  obtain ⟨hBVrep, hBV1, hBV2, hBVdiag, hBVeq, hBVne⟩ := clo_pair_props S
  obtain ⟨hβrep, hβ1, hβ2, hβeq, hβrel, hβne⟩ := clo_betaV_props S
  -- ## Step 6: `ξ` acts transitively on the non-identity elements of both layers
  have hWtrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((cloXiOm h) ^ k) a = b := by
    intro a b ha hb
    have ha1 : (a : P) ≠ 1 := fun hc => ha (Subtype.ext hc)
    have hb1 : (b : P) ≠ 1 := fun hc => hb (Subtype.ext hc)
    have ha2 : orderOf (a : P) = 2 := orderOf_eq_two_of_mem_omega1 h a.2 ha1
    have hb2 : orderOf (b : P) = 2 := orderOf_eq_two_of_mem_omega1 h b.2 hb1
    obtain ⟨k, hk⟩ := h.trans (a : P) (b : P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [cloXiOm_pow_apply]; exact hk)⟩
  have hSMpow : ∀ (k : ℕ) (x : ↥C ⧸ (A.subgroupOf C)),
      ((cloXiOm h) ^ k) (cloSM S x)
        = cloSM S (((cloXiQuot h hA.map_eq hCinv) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have h1 : (cloXiOm h ^ (k + 1)) (cloSM S x)
            = (cloXiOm h ^ k) (cloXiOm h (cloSM S x)) := by
          rw [pow_succ]
          exact Equiv.Perm.mul_apply
            (f := ((cloXiOm h ^ k : ↥(omega1 P) ≃* ↥(omega1 P)) : Equiv.Perm ↥(omega1 P)))
            (g := (cloXiOm h : Equiv.Perm ↥(omega1 P))) (cloSM S x)
        have h2 : ((cloXiQuot h hA.map_eq hCinv) ^ (k + 1)) x
            = ((cloXiQuot h hA.map_eq hCinv) ^ k) (cloXiQuot h hA.map_eq hCinv x) := by
          rw [pow_succ]
          exact Equiv.Perm.mul_apply
            (f := (((cloXiQuot h hA.map_eq hCinv) ^ k :
                (↥C ⧸ (A.subgroupOf C)) ≃* (↥C ⧸ (A.subgroupOf C))) :
              Equiv.Perm (↥C ⧸ (A.subgroupOf C))))
            (g := ((cloXiQuot h hA.map_eq hCinv) : Equiv.Perm (↥C ⧸ (A.subgroupOf C)))) x
        rw [h1, hSMeq, ih, h2]
  have hVtrans : ∀ a b : ↥C ⧸ (A.subgroupOf C), a ≠ 1 → b ≠ 1 →
      ∃ k : ℕ, ((cloXiQuot h hA.map_eq hCinv) ^ k) a = b := by
    intro a b ha hb
    have ha' : cloSM S a ≠ 1 :=
      fun hc => ha (hSMinj (show cloSM S a = cloSM S 1 from by rw [hSM1]; exact hc))
    have hb' : cloSM S b ≠ 1 :=
      fun hc => hb (hSMinj (show cloSM S b = cloSM S 1 from by rw [hSM1]; exact hc))
    obtain ⟨k, hk⟩ := hWtrans (cloSM S a) (cloSM S b) ha' hb'
    exact ⟨k, hSMinj (by rw [← hSMpow k a]; exact hk)⟩
  -- ## Step 7: the algebraic core of Higman's §4 Lemma 6
  exact HS.core_mul (fun v => cloQuot_sq_one hC2 v)
    (fun w => Subtype.ext (by
      have h1 := h.omega1_sq_eq_one w.2
      rw [pow_two] at h1
      simpa using h1))
    hn2 hVcard hWcard (cloXiQuot h hA.map_eq hCinv) (cloXiOm h) hVtrans hWtrans
    (cloBPair S) hBV1 hBV2 hBVdiag hBVeq hBVne
    (cloSM S) hSM1 hSMeq hSMpol
    (fun a ha hc => ha (hSMinj (show cloSM S a = cloSM S 1 from by rw [hSM1]; exact hc)))
    (cloBetaV S) hβ1 hβ2 hβeq hβrel hβne

/-- **Higman 1963, Suzuki 2-groups, p. 87, auxiliary result 8.** Let `A` be a normal abelian
`ξ`-subgroup of a Suzuki 2-group `P` and `C > A` a normal `ξ`-subgroup covering `A`. If `C² ≤ A`
and `C' = ⁅C,C⁆ = A`, then `A ≤ Ω₁(P)`, i.e. `a * a = 1` for all `a ∈ A`.

Route: for `A ≠ ⊥` one has `Ω₁(P) ≤ A`; assuming `A ^ 2 ≠ ⊥` one gets `C² = C' = A` and the lower
central series `C > A > A² > A⁴ = …`, whose factors `L₂ = A/A²` and `L₃ = A²/A⁴` are
`ξ`-isomorphic via the squaring map, contradicting Higman's §4 non-isomorphism result.  A detailed
route reducing the eigenvalue bookkeeping to the arithmetic input in
`Submission.Work.Higman.pow_two_mod_unique` (complete) is in
`Submission/Work/Higman/higman_lemma8_plan.md`; proved preparatory material is in
`Submission/Work/Higman/higman_lemma8.lean`. -/
theorem clo_lemma8 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) :
    ∀ a ∈ A, a * a = 1 := by
  by_cases hA0 : A = ⊥
  · subst hA0
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    simp
  · by_cases hA2 : Work.Higman.powSub A 2 = ⊥
    · intro a ha
      have h2 : a ^ 2 ∈ Work.Higman.powSub A 2 := pow_mem_powSub ha
      rw [hA2, Subgroup.mem_bot] at h2
      rwa [← pow_two]
    · exact (clo_hard h hA hCn hCinv hAC hCA hcover hC2 hCd hA0 hA2).elim

end Work.Higman
