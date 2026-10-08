import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Hering.AppVII.Defs
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Hering.AppVII.appVII_special
import Submission.Work.Hering.AppVII.collapse_solvable
import Submission.Work.Hering.AppVII.hcent_of_eq_bot
import Submission.Work.Hering.AppVII.ker_eq_bot
import Submission.Work.GroupTheory.SylowIUnionTop
import Submission.Work.Coprime.exists_invariant_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII of Peterfalvi I (p. 216) — the final reduction

This file proves `AppVIIProp` (`Submission/Work/Hering/AppVII/Defs.lean`) by strong induction on
`Nat.card A * Nat.card K`, following Peterfalvi's Part 1 (the reduction to the "special
configuration") and Part 2 (the character theory, `Work.Hering.AppVII.appVII_special`).

Let `A = Q ⋊ P` act on `K` by group automorphisms with `|P| = p` prime, `p ∤ |Q|`,
`|C_Q(P)|` odd, `(|K|,|A|) = 1`, and let `Z := appVIIZ A P Q K = ⟨C_K(⁅P,Q⁆), C_K(P^x), x ∈ Q⟩`.

* If `A` or `K` is solvable then `K` has an `A`-invariant Sylow `q`-subgroup for every prime `q`
  (`Work.Coprime.exists_invariant_sylow`).  Each of them is a proper `A`-invariant subgroup, so by
  the induction hypothesis (`map_subtype_appVIIZ_le`) it lies in `Z`; since the invariant Sylows
  generate `K` (`Work.GroupTheory.SylowIUnionTop`), this forces `Z = ⊤` unless `K` is an `r`-group.
  In the remaining case `K` is an `r`-group, hence nilpotent and solvable; then:
  * `Φ(K) ≤ Z` by induction, whence `Z ⊴ K` (a subgroup containing `Φ(K)` of a nilpotent group);
  * if some nontrivial proper `A`-invariant normal `N ⊴ K` is solvable, then lifting fixed points
    from `K ⧸ N` (`Work.Hering.AppVII.collapse_solvable`, coprime Gaschütz with a solvable
    coefficient) gives `Z = ⊤`;
  * so the derived subgroup and `Ω₁(K)` must be all of `K`, which makes `Z = ⊤`; hence `K` is
    abelian of exponent `r`.  Then `K` is an elementary abelian `r`-group and either `Z = ⊤` or
    (`K` being `A`-irreducible) `Z = ⊥` and `C_K(P) = C_K(⁅P,Q⁆) = 1`, in which case
    `Work.Hering.AppVII.appVII_special` (Peterfalvi's Part 2) gives a contradiction.
* If neither `A` nor `K` is solvable, this is `Work.Hering.AppVII.nonsolvable_K`.

The definitions `appVIIF1`, `appVIIFx`, `appVIIZ`, the induction statement `AppVIIStmt` and their
API live in `Submission/Work/Hering/AppVII/Setup.lean` (imported by this file).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Pointwise commutatorElement
open scoped IsMulCommutative

namespace Work.Hering.AppVII

universe u v

/-- `FT.IsInvariant` from the pointwise condition. -/
theorem isInvariant_of_smul_mem {A : Type*} {K : Type*} [Group A] [Group K]
    [MulDistribMulAction A K] (M : Subgroup K) (h : ∀ a : A, ∀ x ∈ M, a • x ∈ M) :
    FT.IsInvariant A M :=
  ⟨fun a => le_antisymm
    (fun x hx => by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have h1 := h a (a⁻¹ • x) hx
      rwa [smul_inv_smul] at h1)
    (fun x hx => by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      exact h a⁻¹ x hx)⟩

/-- The underlying subgroup of an `A`-invariant Sylow subgroup is `A`-invariant. -/
theorem isInvariant_sylow_of_smul {A : Type*} {K : Type*} [Group A] [Group K]
    [MulDistribMulAction A K] (r : ℕ) (S : Sylow r K) (h : ∀ a : A, a • S = S) :
    FT.IsInvariant A (S : Subgroup K) :=
  ⟨fun a => by
    have h1 := congrArg (fun T : Sylow r K => (T : Subgroup K)) (h a)
    rwa [Sylow.pointwise_smul_def] at h1⟩

/-! ## The Feit–Thompson-free form is not available

An earlier version of this file proved the unconditional `AppVIIProp` by strong induction, with
the case in which neither `A` nor `K` is solvable delegated to
`Work.Hering.AppVII.nonsolvable_K`.  That case is *exactly* Feit–Thompson: for coprime orders one
of `|A|`, `|K|` is odd, so with `FeitThompsonProp` the case cannot occur at all.  Both
`appVII_aux` and `nonsolvable_K` therefore carried `sorryAx` (through the project's single open
hole `Work.Skeleton.minSimpleOdd_false`), and they have been removed from the build.

The two honest, axiom-clean forms are:

* `appVII_of_FT (hFT : Submission.Blueprint.FeitThompsonProp) : AppVIIProp` (below) — the form
  used by area `Hering`, with a complete proof resting only on `propext`, `Quot.sound`,
  `Classical.choice` and `hFT`;
* `Work.Hering.AppVII.appVII_of_solvable`, `appVII_of_solvable_K`, `appVII_of_solvable_A` and
  `AppVIIPropSolvableSide` (`appVII_solvable.lean`, `appVIIProp_solvable.lean`) — the
  Feit–Thompson-free form for configurations with a solvable side, which covers every application
  of Appendix VII in this project (in Hering's theorem `K = V` is an elementary abelian
  `2`-group; in area `NormalComplement` it is abelian).
-/


/-! ## Appendix VII with the Feit–Thompson hypothesis — the usable form

`AppVIIProp` (`Submission/Work/Hering/AppVII/Defs.lean`) omits the Feit–Thompson hypothesis that
its proof requires (see the docstring of `appVII` above).  Below is the same theorem *with* that
hypothesis, following the convention of `Submission/Blueprint/Interfaces.lean`: a complete proof,
resting only on `propext`, `Quot.sound` and `Classical.choice` plus the hypothesis `hFT`.

The only difference from `appVII_aux` is that the disjunction `IsSolvable A ∨ IsSolvable K` — which
is what the coprime-action inputs of the reduction need (`Work.Coprime.exists_invariant_sylow`
together with the solvable-coefficient collapse `Work.Hering.AppVII.collapse_solvable`) — is
*proved* from `hFT` and the coprimality of `|K|` and `|A|` instead of being assumed, and the
`nonsolvable_K` branch is dropped. -/

/-- Of two coprime natural numbers, one is odd (more precisely: not both are even).  Hence, by the
odd order theorem, one of the two sides of a coprime pair of finite groups is solvable. -/
theorem isSolvable_or_of_coprime {A K : Type} [Group A] [Finite A] [Group K] [Finite K]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) :
    Group.IsSolvable A ∨ Group.IsSolvable K := by
  rcases Nat.even_or_odd (Nat.card A) with hA | hA
  · refine Or.inr (hFT K ?_)
    rcases Nat.even_or_odd (Nat.card K) with hK | hK
    · exact absurd (Nat.eq_one_of_dvd_coprimes hcop (even_iff_two_dvd.mp hK)
        (even_iff_two_dvd.mp hA)) (by norm_num)
    · exact hK
  · exact Or.inl (hFT A hA)

/-- **The strong induction of Appendix VII, with the Feit–Thompson hypothesis.**  Peterfalvi I,
Appendix VII at the fixed value `Nat.card A * Nat.card K = n` of the induction measure, for
configurations whose two sides are covered by `hFT` (which, for a *coprime* pair, is automatic:
one of the two orders is odd). -/
theorem appVII_aux_of_FT (hFT : Submission.Blueprint.FeitThompsonProp) :
    ∀ n : ℕ, AppVIIStmt.{0, 0} n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro A instA finA P Q hQn hinf hsup p hp hcardP hpQ K instK finK instAct hcop hodd hsize
    classical
    haveI : Fact p.Prime := ⟨hp⟩
    have hsol : Group.IsSolvable A ∨ Group.IsSolvable K := isSolvable_or_of_coprime hFT hcop
    by_contra hZne
    -- ## Step 0: `K` is nontrivial
    have hKne : Nontrivial K := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      refine hZne ((Subgroup.eq_top_iff' _).mpr fun x => ?_)
      have hx : x = 1 := Subsingleton.elim x 1
      rw [hx]
      exact Subgroup.one_mem _
    have hcardK : Nat.card K ≠ 1 := by
      intro h1
      obtain ⟨x, y, hxy⟩ := exists_pair_ne K
      exact hxy ((Nat.card_eq_one_iff_unique.mp h1).1.elim x y)
    -- ## Step 1: the collapse tool
    have hC1 : ∀ (N : Subgroup K) [N.Normal] [FT.IsInvariant A N], N ≠ ⊥ → N ≠ ⊤ →
        ¬ Group.IsSolvable ↥N := by
      intro N hNn hNi hNbot hNtop hNsol
      exact hZne (collapse_solvable ih P Q hQn hinf hsup p hp hcardP hpQ hcop hodd hsize N
        hNbot hNtop hNsol)
    -- ## Step 2: `K` is an `r`-group for some prime `r`
    have hPgroup : ∃ r : ℕ, r.Prime ∧ IsPGroup r K := by
      by_contra hcon
      push_neg at hcon
      let syl : ∀ (q : ℕ), q.Prime → Sylow q K := fun q hq => by
        haveI : Fact q.Prime := ⟨hq⟩
        exact Classical.choose (Work.Coprime.exists_invariant_sylow A hcop.symm hsol q)
      have hspec : ∀ (q : ℕ) (hq : q.Prime), ∀ a : A, a • syl q hq = syl q hq := by
        intro q hq
        haveI : Fact q.Prime := ⟨hq⟩
        exact Classical.choose_spec (Work.Coprime.exists_invariant_sylow A hcop.symm hsol q)
      have hle : ∀ (q : ℕ) (hq : q.Prime),
          ((syl q hq : Sylow q K) : Subgroup K) ≤ appVIIZ A P Q K := by
        intro q hq
        haveI : Fact q.Prime := ⟨hq⟩
        haveI : FT.IsInvariant A (syl q hq : Subgroup K) :=
          isInvariant_sylow_of_smul q (syl q hq) (hspec q hq)
        have hSne : (syl q hq : Subgroup K) ≠ ⊤ := by
          intro htop
          refine hcon q hq ?_
          refine IsPGroup.iff_card.mpr ?_
          obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (syl q hq).isPGroup'
          rw [htop] at hm
          exact ⟨m, by rw [← hm]; exact (Nat.card_congr
            (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K)).symm⟩
        have hcardlt : Nat.card ↥(syl q hq : Subgroup K) < Nat.card K := by
          have h1 : Nat.card ↥(syl q hq : Subgroup K) * (syl q hq : Subgroup K).index =
              Nat.card K := Subgroup.card_mul_index _
          have h2 : 2 ≤ (syl q hq : Subgroup K).index := by
            have hne : (syl q hq : Subgroup K).index ≠ 1 := fun h =>
              hSne (Subgroup.index_eq_one.mp h)
            have hpos : 0 < (syl q hq : Subgroup K).index :=
              Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
            omega
          have hpos : 0 < Nat.card ↥(syl q hq : Subgroup K) := Nat.card_pos
          nlinarith
        have hlt : Nat.card A * Nat.card ↥(syl q hq : Subgroup K) < n := by
          rw [← hsize]
          exact Nat.mul_lt_mul_of_pos_left hcardlt (Nat.card_pos (α := A))
        have hcopSub : Nat.Coprime (Nat.card ↥(syl q hq : Subgroup K)) (Nat.card A) :=
          Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) hcop
        have hIH := ih (Nat.card A * Nat.card ↥(syl q hq : Subgroup K)) hlt P Q hQn hinf hsup p
          hp hcardP hpQ hcopSub hodd rfl
        intro x hx
        have h1 : (⟨x, hx⟩ : ↥(syl q hq : Subgroup K)) ∈
            appVIIZ A P Q ↥(syl q hq : Subgroup K) := by
          rw [hIH]
          exact Subgroup.mem_top _
        exact map_subtype_appVIIZ_le (P := P) (Q := Q) (M := (syl q hq : Subgroup K))
          (Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h1, rfl⟩)
      have htop : (⊤ : Subgroup K) ≤ appVIIZ A P Q K := by
        rw [← Work.GroupTheory.SylowIUnionTop syl]
        exact iSup_le fun q => iSup_le (hle q)
      exact absurd (le_antisymm le_top htop) hZne
    obtain ⟨r, hr, hPgrp⟩ := hPgroup
    haveI : Fact r.Prime := ⟨hr⟩
    have hrK : r ∣ Nat.card K := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPgrp
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hm
        exact hcardK hm
      rw [hm]
      exact dvd_pow_self r hm0
    have hKsol : Group.IsSolvable K := by
      haveI : Group.IsNilpotent K := hPgrp.isNilpotent
      infer_instance
    -- ## Step 3: `K` is abelian
    have hcomm : commutator K = ⊥ := by
      by_contra hne
      by_cases htop : commutator K = ⊤
      · haveI : Group.IsPerfect K := ⟨htop⟩
        exact Group.IsPerfect.not_isSolvable K hKsol
      · haveI : (commutator K).Normal := Subgroup.commutator_normal (⊤ : Subgroup K) ⊤
        haveI : FT.IsInvariant A (commutator K) :=
          FT.IsInvariant.of_characteristic (Subgroup.commutator_characteristic (⊤ : Subgroup K) ⊤)
        refine (hC1 (commutator K) hne htop) ?_
        haveI : Group.IsSolvable K := hKsol
        infer_instance
    have hKcomm : IsMulCommutative K := (commutator_eq_bot_iff K).mp hcomm
    haveI : IsMulCommutative K := hKcomm
    -- ## Step 4: `K` has exponent `r`
    have hKexp : ∀ x : K, x ^ r = 1 := by
      have hOm : FT.omega1 r K = ⊤ := by
        haveI : (FT.omega1 r K).Normal := Subgroup.normal_of_isMulCommutative _
        haveI : FT.IsInvariant A (FT.omega1 r K) := FT.instIsInvariantOmega1 (A := A) r
        by_contra hne
        refine (hC1 (FT.omega1 r K) ?_ hne) ?_
        · intro hbot
          haveI : Fintype K := Fintype.ofFinite K
          obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card r
            (by rwa [Nat.card_eq_fintype_card] at hrK)
          have hxmem : x ∈ FT.omega1 r K :=
            FT.mem_omega1 (p := r) (x := x) (by rw [← hx]; exact pow_orderOf_eq_one x)
          rw [hbot] at hxmem
          have hx1 : x = 1 := by simpa using hxmem
          rw [hx1, orderOf_one] at hx
          exact hr.ne_one hx.symm
        · exact Group.isSolvable_of_comm fun a b =>
            Subtype.ext (mul_comm (a : K) (b : K))
      intro x
      let H : Subgroup K :=
        { carrier := {y : K | y ^ r = 1}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            rw [mul_pow, ha, hb, mul_one]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at ha ⊢
            rw [inv_pow, ha, inv_one] }
      have hle : FT.omega1 r K ≤ H := by
        rw [FT.omega1_le_iff]
        intro y hy
        exact hy
      exact hle (hOm ▸ Subgroup.mem_top x)
    -- ## Step 5: `K` is `A`-irreducible
    have hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤ := by
      intro M hMinv hMbot
      by_contra hMtop
      haveI : M.Normal := Subgroup.normal_of_isMulCommutative M
      haveI : FT.IsInvariant A M := isInvariant_of_smul_mem M hMinv
      refine (hC1 M hMbot hMtop) ?_
      haveI : Group.IsSolvable K := hKsol
      infer_instance
    -- ## Step 6: the special configuration, or `appVIIZ` is all of `K`
    by_cases hZbot : appVIIZ A P Q K = ⊥
    · have hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1 := by
        intro a ha
        have hker : a ∈ (MulDistribMulAction.toMulAut A K).ker := by
          rw [MonoidHom.mem_ker]
          ext x
          simpa using ha x
        rw [ker_eq_bot ih P Q hQn hinf hsup p hp hcardP hpQ hcop hodd hsize hZbot hKne] at hker
        simpa using hker
      have hcent := hcent_of_eq_bot ih P Q hQn hinf hsup p hp hcardP hpQ hcop hodd hsize hZbot
        hfaith
      have hPfpf : appVIIFx A P Q K 1 = ⊥ :=
        le_bot_iff.mp (hZbot ▸ appVIIFx_le_appVIIZ A P Q K 1)
      have hNfix : appVIIF1 A P Q K = ⊥ :=
        le_bot_iff.mp (hZbot ▸ appVIIF1_le_appVIIZ A P Q K)
      exact (appVII_special (A := A) P Q hQn hinf hsup hp hcardP hpQ hodd hcop hr hKexp hKcomm
        hKne hirr hfaith hPfpf hNfix hcent).elim
    · refine hZne (hirr (appVIIZ A P Q K) (fun a x hx => ?_) hZbot)
      have hmem : a • x ∈ a • appVIIZ A P Q K := Subgroup.smul_mem_pointwise_smul x a _ hx
      rwa [smul_appVIIZ_eq_self (K := K) hQn hsup a] at hmem

/-- **Peterfalvi I, Appendix VII, with the Feit–Thompson hypothesis** — the form in which the
lemma is available in this workspace (convention of `Submission/Blueprint/Interfaces.lean`), and
the form an area theorem may assume, like `Work.NormalComplement.Design.AppVIIProp`. -/
theorem appVII_of_FT (hFT : Submission.Blueprint.FeitThompsonProp) : AppVIIProp := by
  intro A instA finA P Q hQn hinf hsup p hp hcardP hpQ K instK finK instAct hcop hodd
  exact AppVIIStmt_univ_indep (appVII_aux_of_FT hFT (Nat.card A * Nat.card K))
    P Q hQn hinf hsup p hp hcardP hpQ hcop hodd rfl

end Work.Hering.AppVII
