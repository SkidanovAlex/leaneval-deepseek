/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DSTR area (fundmath3-gorenstein_walter), `Work.DSTR.d16`
-/
import Mathlib
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.D16Basic
import Submission.Work.DSTR.D16.case1
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE2A.lemma24
import Submission.Work.CORE2A.thm26_aux

open scoped MatrixGroups IsMulCommutative

namespace Work.DSTR.D16

open Subgroup

/-! ## Auxiliary facts about small groups -/

/-- A normal subgroup of order at most `2` is contained in the centre: if `n ≠ 1` lay in `N ⊴ G`
and `g n g⁻¹ ≠ n`, then `1`, `n`, `g n g⁻¹` would be three distinct elements of `N`. -/
theorem le_center_of_normal_card_le_two {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (h : Nat.card ↥N ≤ 2) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hn1 : n = 1
  · rw [hn1, mul_one, one_mul]
  · have hconj : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› n hn g
    have hne1 : g * n * g⁻¹ ≠ 1 := by
      intro hh
      refine hn1 ?_
      have h2 : g⁻¹ * (g * n * g⁻¹) * g = n := by group
      rw [hh] at h2
      simpa using h2.symm
    have hconj_eq : g * n * g⁻¹ = n := by
      by_contra hne
      have h3 : 3 ≤ Nat.card ↥N := by
        have hset : ({1, n, g * n * g⁻¹} : Set G) ⊆ (N : Set G) := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact N.one_mem
          · exact hn
          · exact hconj
        have hcard : ({1, n, g * n * g⁻¹} : Set G).ncard = 3 := by
          have h1 : (1 : G) ∉ ({n, g * n * g⁻¹} : Set G) := by
            intro hmem
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
            rcases hmem with hmem | hmem
            · exact hn1 hmem.symm
            · exact hne1 hmem.symm
          have h2 : n ∉ ({g * n * g⁻¹} : Set G) := by
            intro hmem
            simp only [Set.mem_singleton_iff] at hmem
            exact hne hmem.symm
          rw [show ({1, n, g * n * g⁻¹} : Set G) = insert 1 (insert n {g * n * g⁻¹}) from rfl,
            Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
        calc 3 = ({1, n, g * n * g⁻¹} : Set G).ncard := hcard.symm
          _ ≤ (N : Set G).ncard := Set.ncard_le_ncard hset
          _ = Nat.card ↥(N : Set G) := (Nat.card_coe_set_eq (N : Set G)).symm
      omega
    have : g * n = n * g := by
      have hh := congrArg (fun z => z * g) hconj_eq
      simpa [mul_assoc] using hh
    exact this

/-- `S₃` has no nontrivial normal subgroup of order at most `2`. -/
theorem permFin3NoNormalTwo (N : Subgroup (Equiv.Perm (Fin 3))) (hN : N.Normal)
    (h : Nat.card ↥N ≤ 2) : N = ⊥ := by
  haveI : N.Normal := hN
  have htriv : ∀ τ : Equiv.Perm (Fin 3),
      (∀ σ : Equiv.Perm (Fin 3), σ * τ = τ * σ) → τ = 1 := by decide
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact htriv x (Subgroup.mem_center_iff.mp (le_center_of_normal_card_le_two N h hx))

/-- If `H ⊓ ker f = ⊥` then `f` restricts to an isomorphism `H ≃ H.map f`. -/
noncomputable def mulEquivMapOfDisjointKer {G N : Type*} [Group G] [Group N] (f : G →* N)
    (H : Subgroup G) (h : H ⊓ f.ker = ⊥) : ↥H ≃* ↥(H.map f) := by
  let g : ↥H →* ↥(H.map f) :=
    { toFun := fun a => ⟨f (a : G), Subgroup.mem_map_of_mem f a.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : G) (b : G)) }
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : f (a : G) = f (b : G) := Subtype.ext_iff.mp hab
    have h2 : (a : G)⁻¹ * (b : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (a : G)⁻¹ * (b : G) ∈ H := mul_mem (inv_mem a.2) b.2
    have h4 : (a : G)⁻¹ * (b : G) ∈ H ⊓ f.ker := ⟨h3, h2⟩
    rw [h] at h4
    have h5 : (a : G)⁻¹ * (b : G) = 1 := by simpa using h4
    exact Subtype.ext (inv_mul_eq_one.mp h5)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact MulEquiv.ofBijective g ⟨hinj, hsurj⟩

/-- Restriction of an automorphism of `G` to the set of non-identity elements. -/
noncomputable def restrictNeOne (G : Type*) [Group G] :
    MulAut G →* Equiv.Perm {x : G // x ≠ 1} where
  toFun σ := Equiv.Perm.subtypePerm σ.toEquiv fun x => by
    constructor
    · intro h hx
      exact h (by rw [hx]; exact map_one σ)
    · intro hx h
      exact hx (σ.injective (h.trans (map_one σ).symm))
  map_one' := by ext x; rfl
  map_mul' := by intro σ τ; ext x; rfl

/-- An automorphism of a group is determined by its restriction to the non-identity elements. -/
theorem restrictNeOne_injective (G : Type*) [Group G] : Function.Injective (restrictNeOne G) := by
  intro σ τ hστ
  refine MulEquiv.ext (fun v => ?_)
  by_cases hv : v = 1
  · rw [hv, map_one, map_one]
  · have h := DFunLike.congr_fun hστ (⟨v, hv⟩ : {x : G // x ≠ 1})
    simp only [restrictNeOne, Equiv.Perm.subtypePerm_apply] at h
    have h2 : σ.toEquiv v = τ.toEquiv v := by
      simpa using Subtype.ext_iff.mp h
    simpa using h2

/-! ## `S₃ ≅ D₃` -/

/-- The 3-cycle `0 ↦ 2 ↦ 1 ↦ 0` in `Equiv.Perm (Fin 3)`. -/
noncomputable def rot3 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

/-- The transposition `0 ↦ 1` in `Equiv.Perm (Fin 3)`. -/
noncomputable def tau3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The explicit bijection `Equiv.Perm (Fin 3) → DihedralGroup 3` given by
`1 ↦ 1`, `rot ↦ r 1`, `rot^2 ↦ r 2`, `tau ↦ sr 0`, `rot * tau ↦ sr 2`, `rot^2 * tau ↦ sr 1`. -/
noncomputable def permToD3 (σ : Equiv.Perm (Fin 3)) : DihedralGroup 3 :=
  if σ = 1 then 1
  else if σ = rot3 then DihedralGroup.r 1
  else if σ = rot3 ^ 2 then DihedralGroup.r 2
  else if σ = tau3 then DihedralGroup.sr 0
  else if σ = rot3 * tau3 then DihedralGroup.sr 2
  else DihedralGroup.sr 1

theorem permToD3_one : permToD3 1 = 1 := by decide

theorem permToD3_mul : ∀ a b : Equiv.Perm (Fin 3),
    permToD3 (a * b) = permToD3 a * permToD3 b := by decide

theorem permToD3_injective : Function.Injective permToD3 := by decide

theorem permToD3_surjective : Function.Surjective permToD3 := by decide

/-- `S₃ ≅ D₃`. -/
noncomputable def permFin3MulEquivD3 : Equiv.Perm (Fin 3) ≃* DihedralGroup 3 :=
  MulEquiv.ofBijective
    ({ toFun := permToD3, map_one' := permToD3_one, map_mul' := permToD3_mul } :
      Equiv.Perm (Fin 3) →* DihedralGroup 3)
    ⟨permToD3_injective, permToD3_surjective⟩

theorem card_permFin3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

/-- For a `3`-element type `α`, `Equiv.Perm α ≃* DihedralGroup 3`. -/
theorem permMulEquivDihedralThree (α : Type) [Fintype α] (h : Nat.card α = 3) :
    Nonempty (Equiv.Perm α ≃* DihedralGroup 3) := by
  have h' : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact h
  let e : α ≃ Fin 3 := Fintype.equivOfCardEq (by rw [h', Fintype.card_fin])
  exact ⟨(MulEquiv.mk e.permCongr (fun p q => e.permCongr_mul p q)).trans permFin3MulEquivD3⟩

/-! ## `Q/V` acts faithfully on a Klein four-group `V` -/

/-- If `V ◁ Q` is a Klein four-group with `C_Q(V) = V` then `Q/V` embeds into `Perm (Fin 3)`:
`Q` acts on `V` by conjugation, the kernel of this action is `C_Q(V) = V`, and an automorphism of
`V` is determined by its action on the three non-identity elements. -/
theorem fourGroupQuotientInjection {Q : Type} [Group Q] [Finite Q] (V : Subgroup Q) [V.Normal]
    (hV : Work.GW2.IsFourGroup V) (hC : Subgroup.centralizer (V : Set Q) = V) :
    ∃ ψ : (Q ⧸ V) →* Equiv.Perm (Fin 3), Function.Injective ψ := by
  haveI : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV
  -- the conjugation action `Q →* MulAut V` has kernel `C_Q(V) = V`
  have hker : (MulAut.conjNormal : Q →* MulAut ↥V).ker = V := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      rw [← hC, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ((MulAut.conjNormal g) (⟨v, hv⟩ : ↥V)) = ⟨v, hv⟩ := by rw [hg]; rfl
      have h2 : g * v * g⁻¹ = v := by
        have h3 := congrArg (fun w : ↥V => (w : Q)) h1
        simpa only [MulAut.conjNormal_apply, Subtype.coe_mk] using h3
      have h4 := congrArg (fun z => z * g) h2
      simpa [mul_assoc] using h4.symm
    · intro hg
      refine MulEquiv.ext (fun v => ?_)
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hmem : (g : Q) ∈ V := hg
      have hcomm : (g : Q) * (v : Q) = (v : Q) * g :=
        congrArg Subtype.val (mul_comm (⟨g, hmem⟩ : ↥V) v)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the induced injective map on `Q ⧸ V`
  set Φ : (Q ⧸ V) →* MulAut ↥V :=
    QuotientGroup.lift V MulAut.conjNormal (le_of_eq hker.symm) with hΦdef
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V y
    rw [hΦdef] at hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
    rw [QuotientGroup.lift_mk', QuotientGroup.lift_mk'] at hxy
    have hmem : a⁻¹ * b ∈ V := by
      have h2 : (MulAut.conjNormal : Q →* MulAut ↥V) (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hxy, inv_mul_cancel]
      rw [← hker, MonoidHom.mem_ker]
      exact h2
    have h3 : ((QuotientGroup.mk' V) (a⁻¹ * b)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    exact inv_mul_eq_one.mp (by rw [← map_inv, ← map_mul]; exact h3)
  -- transport to `Fin 3`
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  haveI : Fintype {x : ↥V // x ≠ 1} := Fintype.ofFinite {x : ↥V // x ≠ 1}
  have hcardS : Nat.card {x : ↥V // x ≠ 1} = 3 := by
    have h0 : Nat.card {x : ↥V // x ≠ 1} = ({x : ↥V | x ≠ 1} : Set ↥V).ncard := rfl
    rw [h0]
    have hset : ({x : ↥V | x ≠ 1} : Set ↥V) = (Set.univ : Set ↥V) \ {1} := by
      ext x
      simp
    rw [hset]
    have h1 : ((Set.univ : Set ↥V) \ {1}).ncard + 1 = Nat.card ↥V := by
      have h := Set.ncard_sdiff_singleton_add_one (s := (Set.univ : Set ↥V)) (a := 1)
        (Set.mem_univ 1)
      rw [Set.ncard_univ] at h
      omega
    have h2 : Nat.card ↥V = 4 := hV.1
    omega
  let e : {x : ↥V // x ≠ 1} ≃ Fin 3 :=
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardS, Nat.card_eq_fintype_card,
        Fintype.card_fin])
  let tr : Equiv.Perm {x : ↥V // x ≠ 1} ≃* Equiv.Perm (Fin 3) :=
    MulEquiv.mk e.permCongr (fun p q => e.permCongr_mul p q)
  refine ⟨tr.toMonoidHom.comp ((restrictNeOne ↥V).comp Φ), fun x y hxy => ?_⟩
  exact hΦinj ((restrictNeOne_injective ↥V) (MulEquiv.injective tr hxy))

/-! ## Bender 1.6, case 2 -/

/-- **Bender 1.6, case `X/O(X)` has a self-centralizing normal four-group.**  Proof sketch.  Put `Q = X/O(X)` and `A = O_2(X)`; let `V ◁ Q` be a four-group with `C_Q(V) = V`.  Since `Q` is not a `2`-group and `Q/V ↪ MulAut V ≅ S₃` (kernel `C_Q(V) = V`), we have `|Q/V| ∈ {3,6}`, so `O_2(Q/V) = ⊥` (a group of order `3` or `S₃` has no nontrivial normal `2`-subgroup).  Hence `O_2(Q) = V` (`O_2(Q)/V ≤ O_2(Q/V) = ⊥`).

Also `Q` is solvable (`Q/V ↪ S₃`), so `X` is solvable (`hFT` makes the odd-order `O(X)` solvable; glue with `Group.isSolvable_of_subgroup_quotient`).

* If `A = ⊥`: `F(X) = F_{2'}(X)` and Bender 1.2 (`Work.DSTR.fittingSelfCentralizing`) applied to the solvable `X` gives clause (a).
* If `A ≠ ⊥`: the image `π(A) = A·O(X)/O(X) ≅ A` (because `A ⊓ O(X) = ⊥`) is a normal `2`-subgroup of `Q`, so `π(A) ≤ O_2(Q) = V`; hence `|A| ≤ 4`.  If `|A| = 2` then `A ≅ C₂` is normal in `X`, hence central (`Aut C₂ = 1`), giving clause (b).  If `|A| = 4` then `π(A) = V` (both have order `4`), and `X/(A·O(X)) ≅ Q/V` is cyclic of order `3` (if `|Q/V| = 3`) or is `S₃ ≅ D₃` (if `|Q/V| = 6`), while `A` is a four-group, giving clause (c).

REUSE (all proved, same import world): `Work.DSTR.fitting_le_fittingPi_of_pCore_two_eq_bot`,
`Work.DSTR.fittingPi_le'`, `Work.DSTR.pCore_two_inf_oddCore_eq_bot`,
`Work.DSTR.le_piCore_of_normal_isPiGroup'`, `Work.CORE2A.pCore_isPGroup'`,
`Work.CORE2A.pCore_le_sylow'`, `Work.DSTR.fittingSelfCentralizing`; and
`Submission/Work/DSTR/D16/case1.lean` is a worked template for the same style (its helpers
`le_pCore_of_normal_isPGroup'` etc. live in module `Submission.Work.DSTR.D16.case1`).

NOTE: do NOT import the areas `GLUE`/`RED`/`BMAX`/`FUS`: each carries its own copy of the
`Work.GW2` vocabulary and Lean rejects the duplicate names next to `Submission.Work.DSTR.Defs`. -/
theorem case2 : Work.DSTR.D16Case2Prop := by
  intro X _ _ hFT _ hnot2 hV
  obtain ⟨V, hVnorm, hVfour, hVcent⟩ := hV
  haveI hVnormI : V.Normal := hVnorm
  -- notation
  let O : Subgroup X := Work.GW2.oddCore X
  let A : Subgroup X := Work.GW2.pCore 2 X
  let Q : Type := X ⧸ O
  let π : X →* Q := QuotientGroup.mk' O
  -- basic facts
  have hA2 : IsPGroup 2 ↥A := Work.CORE2A.pCore_isPGroup' (X := X) (p := 2)
  have hAinf : A ⊓ O = ⊥ := Work.DSTR.pCore_two_inf_oddCore_eq_bot X
  have hπker : π.ker = O := QuotientGroup.ker_mk' O
  have hVcard : Nat.card ↥V = 4 := hVfour.1
  have hQcard : Nat.card Q = Nat.card (Q ⧸ V) * Nat.card ↥V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  -- `Q/V` embeds into `Perm (Fin 3)`
  obtain ⟨ψ, hψinj⟩ := fourGroupQuotientInjection (Q := Q) V hVfour hVcent
  have hQdvd : Nat.card (Q ⧸ V) ∣ 6 := by
    have h1 : Nat.card (Q ⧸ V) = Nat.card ↥ψ.range :=
      Nat.card_congr (MonoidHom.ofInjective (f := ψ) hψinj).toEquiv
    rw [h1, ← card_permFin3]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  -- `|Q/V| ∈ {3, 6}`
  have hQne1 : Nat.card (Q ⧸ V) ≠ 1 := by
    intro h1
    apply hnot2
    rw [IsPGroup.iff_card]
    exact ⟨2, by rw [hQcard, h1, hVcard]; norm_num⟩
  have hQne2 : Nat.card (Q ⧸ V) ≠ 2 := by
    intro h2
    apply hnot2
    rw [IsPGroup.iff_card]
    exact ⟨3, by rw [hQcard, h2, hVcard]; norm_num⟩
  have hQcases : Nat.card (Q ⧸ V) = 3 ∨ Nat.card (Q ⧸ V) = 6 := by
    have hmem : Nat.card (Q ⧸ V) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
      rw [show ({1, 2, 3, 6} : Finset ℕ) = Nat.divisors 6 from by decide]
      exact Nat.mem_divisors.mpr ⟨hQdvd, by norm_num⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd h hQne1
    · exact absurd h hQne2
    · exact Or.inl h
    · exact Or.inr h
  -- solvability
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Equiv.Perm.isSolvable (α := Fin 3) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  haveI hsolQV : Group.IsSolvable (Q ⧸ V) :=
    Group.isSolvable_of_isSolvable_injective (f := ψ) hψinj
  have hV2 : IsPGroup 2 ↥V := by
    rw [IsPGroup.iff_card]
    exact ⟨2, by rw [hVcard]; norm_num⟩
  haveI : Group.IsSolvable ↥V := by
    haveI : Group.IsNilpotent ↥V := IsPGroup.isNilpotent (p := 2) (G := ↥V) hV2
    exact IsNilpotent.to_isSolvable
  haveI hsolQ : Group.IsSolvable Q := Group.isSolvable_of_subgroup_quotient V
  haveI hsolO : Group.IsSolvable ↥O := hFT ↥O (Work.ASM.oddCore_odd X)
  haveI hsolX : Group.IsSolvable X := by
    haveI : Group.IsSolvable (X ⧸ O) := hsolQ
    exact Group.isSolvable_of_subgroup_quotient O
  -- `π(A)` is contained in `V`
  have hAmap_le : A.map π ≤ V := by
    have hbot : (A.map π).map (QuotientGroup.mk' V) = ⊥ := by
      let L : Subgroup (Q ⧸ V) := (A.map π).map (QuotientGroup.mk' V)
      by_contra hne
      have hL2 : IsPGroup 2 ↥L := hA2.map π |>.map (QuotientGroup.mk' V)
      have hLnorm : L.Normal :=
        Subgroup.Normal.map (inferInstance : (A.map π).Normal) (QuotientGroup.mk' V)
          (QuotientGroup.mk'_surjective V)
      have hLdvd : Nat.card ↥L ∣ 6 := by
        have h1 : Nat.card ↥L = Nat.card ↥(L.map ψ) :=
          (Subgroup.card_map_of_injective (K := L) (f := ψ) hψinj).symm
        rw [h1, ← card_permFin3]
        exact Subgroup.card_subgroup_dvd_card (L.map ψ)
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hL2
      have hmle : m ≤ 2 := by
        have hle : 2 ^ m ≤ 6 := by
          rw [← hm]
          exact Nat.le_of_dvd (by norm_num) hLdvd
        by_contra h
        simp only [not_le] at h
        have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
        norm_num at h8
        omega
      have hmne : m ≠ 2 := by
        intro hm2
        have h4 : 2 ^ m ∣ 6 := by rw [← hm]; exact hLdvd
        rw [hm2] at h4
        norm_num at h4
      have hmle1 : m ≤ 1 := by omega
      have hLle2 : Nat.card ↥L ≤ 2 := by
        rw [hm]
        interval_cases m <;> norm_num
      have hLne1 : Nat.card ↥L ≠ 1 := by
        intro h1
        exact hne (Subgroup.card_eq_one.mp h1)
      have hLpos : 0 < Nat.card ↥L := by
        haveI : Nonempty ↥L := ⟨⟨1, L.one_mem⟩⟩
        exact Nat.card_pos
      have hLc : Nat.card ↥L = 2 := by omega
      have hdvdQV : Nat.card ↥L ∣ Nat.card (Q ⧸ V) := Subgroup.card_subgroup_dvd_card L
      have h6 : Nat.card (Q ⧸ V) = 6 := by
        rcases hQcases with h | h
        · exfalso
          have h2dvd : (2 : ℕ) ∣ Nat.card (Q ⧸ V) := by rw [← hLc]; exact hdvdQV
          rw [h] at h2dvd
          exact absurd h2dvd (by norm_num)
        · exact h
      have htop : ψ.range = ⊤ := by
        refine Subgroup.eq_top_of_card_eq ψ.range ?_
        rw [← Nat.card_congr (MonoidHom.ofInjective (f := ψ) hψinj).toEquiv, h6, card_permFin3]
      have hsurjψ : Function.Surjective ψ := MonoidHom.range_eq_top.mp htop
      have hLmapnorm : (L.map ψ).Normal := hLnorm.map ψ hsurjψ
      have hLmapcard : Nat.card ↥(L.map ψ) = 2 := by
        rw [Subgroup.card_map_of_injective (K := L) (f := ψ) hψinj, hLc]
      have hLbot : L = ⊥ := by
        have hkerbot : ψ.ker = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [Subgroup.mem_bot]
          rw [MonoidHom.mem_ker] at hx
          exact hψinj (by rw [hx, map_one])
        have hle : L ≤ ψ.ker :=
          (Subgroup.map_eq_bot_iff L (f := ψ)).mp
            (permFin3NoNormalTwo (L.map ψ) hLmapnorm (by omega))
        rw [hkerbot] at hle
        exact le_bot_iff.mp hle
      exact hne hLbot
    have h2 := (Subgroup.map_eq_bot_iff (A.map π) (f := QuotientGroup.mk' V)).mp hbot
    rwa [QuotientGroup.ker_mk'] at h2
  have hAcardEq : Nat.card ↥A = Nat.card ↥(A.map π) :=
    Nat.card_congr (mulEquivMapOfDisjointKer π A (by rw [hπker]; exact hAinf)).toEquiv
  have hAle4 : Nat.card ↥A ≤ 4 := by
    have h1 : Nat.card ↥(A.map π) ≤ Nat.card ↥V :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hAmap_le)
        (Subgroup.inclusion_injective hAmap_le)
    omega
  -- `A = ⊥` gives (a)
  by_cases hA : A = ⊥
  · left
    have hF : Work.DSTR.F2p X = Work.GW2.fitting X :=
      le_antisymm (Work.DSTR.fittingPi_le' ({2}ᶜ : Set ℕ) X)
        (Work.DSTR.fitting_le_fittingPi_of_pCore_two_eq_bot X hA)
    show Subgroup.centralizer ((Work.DSTR.F2p X : Subgroup X) : Set X) ≤ Work.DSTR.F2p X
    rw [hF]
    exact Work.DSTR.fittingSelfCentralizing X hsolX
  · -- `A ≠ ⊥`
    have hAne : A ≠ ⊥ := hA
    have hAcard : Nat.card ↥A = 2 ∨ Nat.card ↥A = 4 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
      have hkle : k ≤ 2 := by
        have hle : 2 ^ k ≤ 4 := by rw [← hk]; exact hAle4
        by_contra h
        simp only [not_le] at h
        have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
        norm_num at h8
        omega
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hAne (Subgroup.card_eq_one.mp (by rw [hk]; norm_num))
      interval_cases k
      · exact absurd rfl hk0
      · left; rw [hk]; norm_num
      · right; rw [hk]; norm_num
    rcases hAcard with hA2c | hA4c
    · -- clause (b): `A` has order `2`, so it is central
      right; left
      obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
      refine ⟨(a : X), ?_, ?_⟩
      · exact le_center_of_normal_card_le_two A (by omega) a.2
      · have hdvd : orderOf (a : X) ∣ Nat.card ↥A := Subgroup.orderOf_dvd_natCard A a.2
        rw [hA2c] at hdvd
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) (fun hh => ha (Subtype.ext hh))
        · exact h
    · -- clause (c): `A` is a four-group and `X/(A·O) ≅ Q/V ∈ {C₃, D₃}`
      right; right
      have hmapV : A.map π = V :=
        Subgroup.eq_of_le_of_card_ge hAmap_le (by rw [hVcard, ← hAcardEq, hA4c])
      have hAfour : Work.GW2.IsFourGroup A := by
        refine ⟨hA4c, ?_⟩
        intro v hv
        have eA : ↥A ≃* ↥(A.map π) :=
          mulEquivMapOfDisjointKer π A (by rw [hπker]; exact hAinf)
        have h1 : (eA ⟨v, hv⟩) ^ 2 = 1 := by
          have hmem : ((eA ⟨v, hv⟩ : ↥(A.map π)) : Q) ∈ V := by
            rw [← hmapV]; exact (eA ⟨v, hv⟩).2
          exact Subtype.ext (hVfour.2 ((eA ⟨v, hv⟩ : ↥(A.map π)) : Q) hmem)
        have h2 : (⟨v, hv⟩ : ↥A) ^ 2 = 1 := by
          apply eA.injective
          rw [map_pow, map_one]
          exact h1
        exact congrArg Subtype.val h2
      refine ⟨hAfour, ?_⟩
      -- `X ⧸ (A ⊔ O) ≃* Q ⧸ V`
      let πV : Q →* (Q ⧸ V) := QuotientGroup.mk' V
      have hfker : (πV.comp π).ker = A ⊔ O := by
        have h1 : πV.ker = V := QuotientGroup.ker_mk' V
        rw [← MonoidHom.comap_ker πV π, h1, ← hmapV, Subgroup.comap_map_eq]
        rw [show π.ker = O from QuotientGroup.ker_mk' O]
      have eQ : (X ⧸ (A ⊔ O)) ≃* (Q ⧸ V) := by
        refine MulEquiv.ofBijective (QuotientGroup.lift (A ⊔ O) (πV.comp π) ?_) ⟨?_, ?_⟩
        · rw [hfker]
        · intro x y hxy
          obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (A ⊔ O) x
          obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A ⊔ O) y
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hxy
          rw [QuotientGroup.lift_mk', QuotientGroup.lift_mk'] at hxy
          have hmem : a⁻¹ * b ∈ (πV.comp π).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
          rw [hfker] at hmem
          have h3 : ((QuotientGroup.mk' (A ⊔ O)) (a⁻¹ * b)) = 1 := by
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
            exact hmem
          exact inv_mul_eq_one.mp (by rw [← map_inv, ← map_mul]; exact h3)
        · intro y
          obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective V y
          obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O q
          refine ⟨QuotientGroup.mk' (A ⊔ O) a, ?_⟩
          rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
          rfl
      rcases hQcases with h3 | h6
      · left
        have hcard : Nat.card (X ⧸ (A ⊔ O)) = 3 := by
          rw [Nat.card_congr eQ.toEquiv, h3]
        exact ⟨isCyclic_of_prime_card hcard, hcard⟩
      · right
        have htop : ψ.range = ⊤ := by
          refine Subgroup.eq_top_of_card_eq ψ.range ?_
          rw [← Nat.card_congr (MonoidHom.ofInjective (f := ψ) hψinj).toEquiv, h6, card_permFin3]
        have eP : (Q ⧸ V) ≃* Equiv.Perm (Fin 3) :=
          MulEquiv.ofBijective ψ ⟨hψinj, MonoidHom.range_eq_top.mp htop⟩
        obtain ⟨eD⟩ := permMulEquivDihedralThree (Fin 3)
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
        exact ⟨eQ.trans (eP.trans eD)⟩

end Work.DSTR.D16
