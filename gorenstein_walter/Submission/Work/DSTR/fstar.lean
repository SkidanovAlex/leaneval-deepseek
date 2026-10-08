/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DSTR area (fundmath3-gorenstein_walter)

# `Work.DSTR.fstar`: `C_X(F*(X)) ≤ F*(X)` for `D`-groups

Mathematical plan (Bender 1.6 + Bender 1.2):

* If `X` is solvable then `E(X) = 1`, hence `F*(X) = F(X)` and Bender 1.2 (`he1`) gives
  `C_X(F*(X)) ≤ C_X(F(X)) ≤ F(X) = F*(X)`.
* Bender 1.6 (`h16`) splits into four cases:
  * (a) `C_X(F_{2'}(X)) ≤ F_{2'}(X)` gives the claim directly, since `F_{2'}(X) ≤ F(X) ≤ F*(X)`;
  * (b) `X` has a central involution.  Then `X/O(X)` has non-trivial centre; the shapes of
    `IsDGroup` then force `X/O(X)` to be solvable (a 2-group, or an extension of a
    self-centralizing four-group), so `X` is solvable and the previous bullet applies;
  * (c) `O_2(X)` is a four-group and `X/(O_2(X)·O(X))` is `C₃` or `D₃`, so `X` is solvable;
  * (d) `X` has a normal quasisimple `E` with `X/E` solvable.  Then the centralizer of a
    quasisimple normal subgroup is solvable, and the general lemma
    `le_fstar_of_solvable_centralizer` finishes.
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.ASM.Basic
import Submission.Work.ASM.oddCore_odd
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.D16.case1
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Aut.centralizer
import Submission.Work.DSTR.M110.Aut.pglHomInjective
import Submission.Work.CORE2A.fstar_ne_bot
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.lemma24

open scoped MatrixGroups

namespace Work.DSTR

open Subgroup

/-! ## 0. Toolkit -/

/-- Monotonicity of the centralizer, in the form used below. -/
theorem centralizer_anti {X : Type*} [Group X] {A B : Subgroup X} (h : A ≤ B) :
    Subgroup.centralizer (B : Set X) ≤ Subgroup.centralizer (A : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro a ha
  exact hx a (h ha)

/-! ## 1. A group of cardinality at most six is solvable -/

/-- A finite group of order at most `6` is solvable (orders `1,2,3,4,5,6`; a group of order
`6` has a normal subgroup of order `3` by Cauchy plus Lagrange, and a subgroup of index `2` is
normal). -/
theorem isSolvable_of_card_le_six {H : Type*} [Group H] [Finite H] (h : Nat.card H ≤ 6) :
    Group.IsSolvable H := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  interval_cases hc : Nat.card H
  · haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hc).1
    infer_instance
  · haveI : IsCyclic H := isCyclic_of_prime_card (p := 2) hc
    infer_instance
  · haveI : IsCyclic H := isCyclic_of_prime_card (p := 3) hc
    infer_instance
  · by_cases hex : ∃ a : H, orderOf a = 4
    · obtain ⟨a, ha⟩ := hex
      haveI : IsCyclic H := isCyclic_of_card_le_orderOf a (by rw [ha, hc])
      infer_instance
    · have h2 : ∀ x : H, x ^ 2 = 1 := by
        intro x
        have hdvd : orderOf x ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 from by norm_num, ← hc]
          exact orderOf_dvd_natCard x
        obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        have hjle : j ≤ 1 := by
          by_contra hcon
          have hj2 : j = 2 := by omega
          exact hex ⟨x, by rw [hje, hj2]; norm_num⟩
        have hdvd2 : orderOf x ∣ 2 := by
          rw [hje]
          simpa using Nat.pow_dvd_pow 2 hjle
        exact (orderOf_dvd_iff_pow_eq_one).mp hdvd2
      haveI : IsMulCommutative H := Work.ASM.isMulCommutative_of_forall_sq_eq_one h2
      infer_instance
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI : IsCyclic H := isCyclic_of_prime_card (p := 5) hc
    infer_instance
  · have h3dvd : 3 ∣ Nat.card H := by rw [hc]; norm_num
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have hPcard : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers]; exact ha
    haveI : IsCyclic ↥(Subgroup.zpowers a) := isCyclic_of_prime_card hPcard
    have hidx : (Subgroup.zpowers a).index = 2 := by
      have hix := Subgroup.index_mul_card (H := Subgroup.zpowers a)
      rw [hPcard, hc] at hix
      omega
    haveI : (Subgroup.zpowers a).Normal := Subgroup.normal_of_index_eq_two hidx
    haveI : Group.IsSolvable (H ⧸ Subgroup.zpowers a) := by
      have hcard : Nat.card (H ⧸ Subgroup.zpowers a) = 2 := hidx
      haveI : IsCyclic (H ⧸ Subgroup.zpowers a) := isCyclic_of_prime_card hcard
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient (Subgroup.zpowers a)

/-! ## 2. Automorphisms of a four-group -/

/-- The group of automorphisms of a four-group has at most `6` elements: an automorphism fixes
`1` and permutes the three remaining elements faithfully. -/
theorem natCard_mulAut_le_six_of_card_four {V : Type*} [Group V] (h4 : Nat.card V = 4) :
    Nat.card (MulAut V) ≤ 6 := by
  classical
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  haveI : Fintype V := Fintype.ofFinite V
  let act : MulAut V →* Equiv.Perm {x : V // x ≠ 1} :=
    { toFun := fun φ =>
        { toFun := fun x => ⟨φ x.1, fun h => x.2 (φ.injective (by rw [h, map_one]))⟩
          invFun := fun x => ⟨φ.symm x.1, fun h => x.2 (φ.symm.injective (by rw [h, map_one]))⟩
          left_inv := fun x => by ext; simp
          right_inv := fun x => by ext; simp }
      map_one' := by ext x; rfl
      map_mul' := fun φ ψ => by ext x; rfl }
  have hinj : Function.Injective act := by
    intro φ ψ h
    ext v
    by_cases hv : v = 1
    · rw [hv, map_one, map_one]
    · have h2 := congrArg (fun (σ : Equiv.Perm {x : V // x ≠ 1}) => ((σ ⟨v, hv⟩ : {x : V // x ≠ 1}) : V)) h
      simpa [act] using h2
  have h3 : Fintype.card {x : V // x ≠ 1} = 3 := by
    haveI : Fintype {x : V // x = 1} := Fintype.ofFinite _
    have h1 : Fintype.card {x : V // x = 1} = 1 := Fintype.card_subtype_eq 1
    have hcompl := Fintype.card_subtype_compl (fun x : V => x = 1)
    rw [h1] at hcompl
    have hcard : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card, h4]
    rw [hcompl, hcard]
  have hperm : Nat.card (Equiv.Perm {x : V // x ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]
    norm_num
  have hle := Nat.card_le_card_of_injective act hinj
  omega

/-! ## 3. The four-group shape is solvable -/

/-- **A group with a self-centralizing normal four-group is solvable.** -/
theorem fourGroupSolvable {Q : Type*} [Group Q] (V : Subgroup Q) [V.Normal]
    (hV : Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1)
    (hC : Subgroup.centralizer (V : Set Q) = V) : Group.IsSolvable Q := by
  classical
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.1]; norm_num)
  haveI : Group.IsSolvable ↥V := by
    haveI : IsMulCommutative ↥V :=
      Work.ASM.isMulCommutative_of_forall_sq_eq_one (fun x => by
        have := hV.2 (x : Q) x.2
        simpa using Subtype.ext (by simpa using this : ((x : Q) ^ 2) = ((1 : Q))))
    infer_instance
  -- kernel of the conjugation action
  have hker : (MulAut.conjNormal (G := Q) (H := V)).ker = Subgroup.centralizer (V : Set Q) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg v hv
      have h1 : MulAut.conjNormal g ⟨v, hv⟩ = ⟨v, hv⟩ := by
        have := congrArg (fun φ : MulAut ↥V => (φ ⟨v, hv⟩ : ↥V)) hg
        simpa using this
      have h2 : g * v * g⁻¹ = v := by
        have := congrArg (fun x : ↥V => (x : Q)) h1
        simpa [MulAut.conjNormal_apply] using this
      calc v * g = (g * v * g⁻¹) * g := by rw [h2]
        _ = g * v := by group
    · intro hg
      ext v
      rw [MulAut.conjNormal_apply, (hg v v.2).symm]
      show (v : Q) * g * g⁻¹ = (v : Q)
      group
  -- Q/V embeds into MulAut V, so its order is at most 6
  set φ : Q →* MulAut ↥V := MulAut.conjNormal with hφ
  have hle : V ≤ φ.ker := by rw [hφ, hker, hC]
  let ψ : Q ⧸ V →* MulAut ↥V := QuotientGroup.lift V φ hle
  have hψmk : ∀ x : Q, ψ (QuotientGroup.mk' V x) = φ x := fun x =>
    QuotientGroup.lift_mk' (N := V) (φ := φ) hle x
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    induction x using Quotient.inductionOn with
    | _ a =>
      have h1 : φ a = 1 := by rw [← hψmk a]; exact hx
      have h2 : a ∈ V := by
        have h3 : a ∈ φ.ker := MonoidHom.mem_ker.mpr h1
        rwa [hφ, hker, hC] at h3
      rwa [QuotientGroup.eq_one_iff]
  haveI : Finite (MulAut ↥V) := inferInstance
  haveI : Finite (Q ⧸ V) := Finite.of_injective ψ hinj
  have hcard : Nat.card (Q ⧸ V) ≤ 6 := by
    have h1 : Nat.card (Q ⧸ V) ≤ Nat.card (MulAut ↥V) := Nat.card_le_card_of_injective ψ hinj
    have h2 := natCard_mulAut_le_six_of_card_four hV.1
    omega
  haveI : Group.IsSolvable (Q ⧸ V) := isSolvable_of_card_le_six hcard
  exact Group.isSolvable_of_subgroup_quotient V

/-! ## 4. The centre of the model groups -/

/-- `Z(A₇) = 1`. -/
theorem center_a7 : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
  alternatingGroup.center_eq_bot (α := Fin 7) (by simp)

/-- `Z(PSL(2,q)) = 1` for `q = p^k` odd, `q ≥ 5`. -/
theorem center_PSL (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = ⊥ := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hmem : Work.AUTL2.pslHom (GaloisField p k) z ∈
      Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p k) :
        Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w', rfl⟩ := hw
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_center_iff.mp hz w')
  rw [Work.AUTL2.Aut.centralizer p k hp hq] at hmem
  have h1 : Work.AUTL2.pslHom (GaloisField p k) z = 1 := by simpa using hmem
  have hinj : Function.Injective (Work.AUTL2.pslHom (GaloisField p k)) := by
    intro x y hxy
    have h2 : Matrix.ProjectiveSpecialLinearGroup.toPGL x =
        Matrix.ProjectiveSpecialLinearGroup.toPGL y :=
      Work.AUTL2.Aut.pglHomInjective (GaloisField p k) hxy
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h2
  exact hinj (by rw [h1, map_one])

/-- `Z(PGL(2,q)) = 1` for `q = p^k` odd, `q ≥ 5`. -/
theorem center_PGL (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    Subgroup.center (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) = ⊥ := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hmem : Work.AUTL2.pglHom (GaloisField p k) z ∈
      Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p k) :
        Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w', rfl⟩ := hw
    show Work.AUTL2.pslHom (GaloisField p k) w' * Work.AUTL2.pglHom (GaloisField p k) z =
      Work.AUTL2.pglHom (GaloisField p k) z * Work.AUTL2.pslHom (GaloisField p k) w'
    rw [show Work.AUTL2.pslHom (GaloisField p k) w' =
      Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjectiveSpecialLinearGroup.toPGL w') from rfl]
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subgroup.mem_center_iff.mp hz (Matrix.ProjectiveSpecialLinearGroup.toPGL w'))
  rw [Work.AUTL2.Aut.centralizer p k hp hq] at hmem
  have h1 : Work.AUTL2.pglHom (GaloisField p k) z = 1 := by simpa using hmem
  exact Work.AUTL2.Aut.pglHomInjective (GaloisField p k) (by rw [h1, map_one])
/-! ## 5. Quasisimple groups are not solvable; solvable groups have trivial layer -/

/-- A quasisimple subgroup (as a group) is not solvable: it is perfect and nontrivial. -/
theorem not_isSolvable_of_isQuasisimple {X : Type*} [Group X] {E : Subgroup X}
    (hE : Work.GW2.IsQuasisimple E) : ¬ Group.IsSolvable ↥E := by
  haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hE.2.toNontrivial
  haveI : Nontrivial ↥E :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥E))
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE.1
  exact Group.IsPerfect.not_isSolvable ↥E

/-- `E(X)` is normal in `X`. -/
instance layer_normal (X : Type*) [Group X] : (Work.GW2.layer X).Normal := by
  rw [Work.GW2.layer]
  exact Subgroup.sSup_normal _ (fun E hE => hE.1)

/-- `F*(X)` is normal in `X`. -/
instance fstar_normal (X : Type*) [Group X] : (Work.GW2.fstar X : Subgroup X).Normal := by
  have h : (Work.GW2.fstar X : Subgroup X) = Work.GW2.fitting X ⊔ Work.GW2.layer X := rfl
  rw [h]
  exact Subgroup.sup_normal _ _

/-- For a solvable group `X` the layer is trivial, so `F*(X) = F(X)`. -/
theorem fstar_eq_fitting_of_solvable {X : Type*} [Group X] (h : Group.IsSolvable X) :
    Work.GW2.fstar X = Work.GW2.fitting X := by
  have hlayer : Work.GW2.layer X = ⊥ := by
    rw [Work.GW2.layer]
    refine le_antisymm ?_ bot_le
    refine sSup_le ?_
    rintro E ⟨hEn, hEq⟩
    exact absurd (inferInstance : Group.IsSolvable ↥E) (not_isSolvable_of_isQuasisimple hEq)
  rw [Work.GW2.fstar, hlayer, sup_bot_eq]

/-- If `X` is solvable then `C_X(F*(X)) ≤ F*(X)` (Bender 1.2, `he1`). -/
theorem fstar_le_of_solvable (he1 : Work.GW2.FittingSelfCentralizingProp) (X : Type) [Group X]
    [Finite X] (h : Group.IsSolvable X) :
    Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X) ≤ Work.GW2.fstar X := by
  rw [fstar_eq_fitting_of_solvable h]
  exact he1 X h

/-! ## 6. The centralizer of a normal quasisimple subgroup with solvable quotient -/

/-- If `E ◁ X` is quasisimple and `X/E` is solvable then `C_X(E)` is solvable: its kernel on
`X/E` is `Z(E)` and its image is solvable. -/
theorem solvable_centralizer_of_quasisimple {X : Type*} [Group X] (E : Subgroup X) [E.Normal]
    (hE : Work.GW2.IsQuasisimple E) (h : Group.IsSolvable (X ⧸ E)) :
    Group.IsSolvable ↥(Subgroup.centralizer (E : Set X)) := by
  classical
  set C : Subgroup X := Subgroup.centralizer (E : Set X) with hC
  let f : ↥C →* X ⧸ E := (QuotientGroup.mk' E).comp C.subtype
  haveI : Group.IsSolvable ↥(f.ker) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha : ((a : ↥C) : X) ∈ E := by
      have h1 : f (a : ↥C) = 1 := MonoidHom.mem_ker.mp a.2
      change (QuotientGroup.mk' E ((a : ↥C) : X)) = 1 at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hb : ((b : ↥C) : X) ∈ E := by
      have h1 : f (b : ↥C) = 1 := MonoidHom.mem_ker.mp b.2
      change (QuotientGroup.mk' E ((b : ↥C) : X)) = 1 at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hca : ((a : ↥C) : X) ∈ Subgroup.centralizer (E : Set X) := (a : ↥C).2
    exact Subtype.ext (Subtype.ext ((Subgroup.mem_centralizer_iff.mp hca) _ hb).symm)
  haveI : Group.IsSolvable (↥C ⧸ f.ker) := by
    have e := QuotientGroup.quotientKerEquivRange f
    haveI : Group.IsSolvable ↥(f.range) := inferInstance
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (MulEquiv.surjective e.symm)
  exact Group.isSolvable_of_subgroup_quotient f.ker

/-! ## 7. A solvable `C_X(F*(X))` lies in `F*(X)` -/

/-- If `C_X(F*(X))` is solvable then it is contained in `F*(X)`: its Fitting subgroup is
nilpotent normal in `X`, hence inside `F(X)`, and Bender 1.2 applied to the solvable group
`C_X(F*(X))` gives the claim. -/
theorem solvableCentralizerFstar (he1 : Work.GW2.FittingSelfCentralizingProp)
    (X : Type) [Group X] [Finite X]
    (h : Group.IsSolvable ↥(Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X))) :
    Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X) ≤ Work.GW2.fstar X := by
  classical
  set C : Subgroup X := Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X) with hC
  haveI hCnorm : C.Normal := by rw [hC]; infer_instance
  haveI hCsolv : Group.IsSolvable ↥C := h
  set K : Subgroup X := (Work.GW2.fitting ↥C).map C.subtype with hK
  haveI : (Work.GW2.fitting ↥C).Characteristic := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    infer_instance
  haveI hKnorm : K.Normal := by rw [hK]; infer_instance
  haveI hKnil : Group.IsNilpotent ↥K := by
    rw [hK]
    have h1 : Group.IsNilpotent ↥(Work.GW2.fitting ↥C) := by
      rw [Work.CORE2A.fitting_eq_isaacsFitting]
      infer_instance
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective)).mp h1
  have hKle : K ≤ Work.GW2.fitting X := by
    rw [hK]
    exact Work.CORE2A.le_fitting_of_normal_isNilpotent
  have hCK : C ≤ K := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X) := by
      rw [← hC]; exact hc
    rw [Subgroup.mem_centralizer_iff] at hc'
    have hyK : ∀ y : ↥C, y ∈ Work.GW2.fitting ↥C → (y : X) ∈ K := by
      intro y hy
      rw [hK]
      exact ⟨y, hy, rfl⟩
    have hmem : (⟨c, hc⟩ : ↥C) ∈
        Subgroup.centralizer ((Work.GW2.fitting ↥C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hle' : Work.GW2.fitting X ≤ Work.GW2.fstar X := by
        show Work.GW2.fitting X ≤ Work.GW2.fstar X
        rw [Work.GW2.fstar]
        exact le_sup_left
      exact hc' (y : X) (hle' (hKle (hyK y hy)))
    have h2 : (⟨c, hc⟩ : ↥C) ∈ Work.GW2.fitting ↥C := he1 ↥C hCsolv hmem
    exact ⟨⟨c, hc⟩, h2, rfl⟩
  calc C ≤ K := hCK
    _ ≤ Work.GW2.fitting X := hKle
    _ ≤ Work.GW2.fstar X := by
        show Work.GW2.fitting X ≤ Work.GW2.fstar X
        rw [Work.GW2.fstar]
        exact le_sup_left

/-! ## 8. The join of two normal solvable subgroups is solvable -/

/-- The join of two normal solvable subgroups is solvable. -/
theorem isSolvable_sup_of_normal {G : Type*} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    [Group.IsSolvable ↥H] [Group.IsSolvable ↥K] : Group.IsSolvable ↥(H ⊔ K) := by
  classical
  let g : ↥(H ⊔ K) →* G ⧸ K := (QuotientGroup.mk' K).comp (H ⊔ K).subtype
  have hkerle : g.ker ≤ K.subgroupOf (H ⊔ K) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : g x = 1 := MonoidHom.mem_ker.mp hx
    exact (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' K ((x : ↥(H ⊔ K)) : G)) = 1
      exact hx')
  have hleker : K.subgroupOf (H ⊔ K) ≤ g.ker := by
    intro x hx
    have hx' : ((x : ↥(H ⊔ K)) : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr hx')
  have hker : g.ker = K.subgroupOf (H ⊔ K) := le_antisymm hkerle hleker
  haveI : Group.IsSolvable ↥(g.ker) := by
    have hmap : ∀ x : ↥(g.ker), ((x : ↥(H ⊔ K)) : G) ∈ K := fun x =>
      Subgroup.mem_subgroupOf.mp (hker ▸ x.2)
    refine Group.isSolvable_of_isSolvable_injective
      (f := ({ toFun := fun x => ⟨((x : ↥(H ⊔ K)) : G), hmap x⟩
               map_one' := rfl
               map_mul' := fun a b => rfl } : ↥(g.ker) →* ↥K)) ?_
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥K => (z : G)) h
  haveI : Group.IsSolvable (↥(H ⊔ K) ⧸ g.ker) := by
    have e := QuotientGroup.quotientKerEquivRange g
    have hrange : g.range = H.map (QuotientGroup.mk' K) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff (H := K) (f := QuotientGroup.mk' K)).mpr
          (by rw [QuotientGroup.ker_mk']),
        sup_bot_eq]
    haveI hrange_solv : Group.IsSolvable ↥(g.range) := by
      rw [hrange]
      refine Group.isSolvable_of_surjective
        (f := MonoidHom.codRestrict ((QuotientGroup.mk' K).comp H.subtype)
          (H.map (QuotientGroup.mk' K)) (fun x => ⟨x, x.2, rfl⟩)) ?_
      rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := hy
      exact ⟨⟨h, hh⟩, rfl⟩
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) (MulEquiv.surjective e.symm)
  exact Group.isSolvable_of_subgroup_quotient g.ker

/-! ## 9. Bender 1.6 (b): a `D`-group with a central involution is solvable -/

/-- **Bender 1.6 (b)**: a `D`-group with a central involution is solvable.  Indeed `X/O(X)`
has non-trivial centre, so its shape is that of a `2`-group or of an extension of a
self-centralizing four-group (`A₇`, `L₂(q)`, `PGL₂(q)` have trivial centre). -/
theorem solvable_of_central_involution (X : Type) [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp) (hD : Work.GW2.IsDGroup X)
    (hz : ∃ z : X, z ∈ Subgroup.center X ∧ orderOf z = 2) : Group.IsSolvable X := by
  classical
  obtain ⟨z, hzcen, hzord⟩ := hz
  set O : Subgroup X := Work.GW2.oddCore X with hO
  have hOodd : Odd (Nat.card O) := by rw [hO]; exact Work.ASM.oddCore_odd X
  have hzO : z ∉ O := by
    intro hmem
    have hdvd : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hmem
    have hodd : Odd (orderOf z) := Odd.of_dvd_nat hOodd hdvd
    rw [hzord] at hodd
    exact absurd hodd (by decide)
  have hz2 : z ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hzbar_center : (QuotientGroup.mk' O z : X ⧸ O) ∈ Subgroup.center (X ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzcen w]
  have hzbar_ne : (QuotientGroup.mk' O z : X ⧸ O) ≠ 1 := by
    intro h1
    exact hzO ((QuotientGroup.eq_one_iff z).mp h1)
  have key : Group.IsSolvable (X ⧸ O) → Group.IsSolvable X := by
    intro hQ
    haveI : Group.IsSolvable (X ⧸ O) := hQ
    haveI : Group.IsSolvable ↥O := hFT ↥O hOodd
    exact Group.isSolvable_of_subgroup_quotient O
  have hshape : Work.GW2.DShape (X ⧸ O) := hD
  rcases hshape with h2grp | hfour | hA7 | hL
  · exact key (by
      haveI : Group.IsNilpotent (X ⧸ O) := IsPGroup.isNilpotent (p := 2) h2grp
      exact IsNilpotent.to_isSolvable)
  · obtain ⟨V, hVn, hV4, hVc⟩ := hfour
    exact key (by
      haveI : V.Normal := hVn
      exact fourGroupSolvable V hV4 hVc)
  · obtain ⟨e⟩ := hA7
    exfalso
    have hzc : e (QuotientGroup.mk' O z) ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨_, hzbar_center, rfl⟩
    rw [center_a7] at hzc
    have h1 : e (QuotientGroup.mk' O z) = 1 := by simpa using hzc
    exact hzbar_ne (e.injective (by rw [h1, map_one]))
  · obtain ⟨L, hLn, hLodd, p, k, hp, hpo, hq, hLiso⟩ := hL
    haveI : Fact p.Prime := hp
    exfalso
    have hzbar2 : (QuotientGroup.mk' O z : X ⧸ O) ^ 2 = 1 := by
      rw [← map_pow, hz2]
      simp
    have hzbarL : (QuotientGroup.mk' O z : X ⧸ O) ∈ L := by
      have hdvd : orderOf (QuotientGroup.mk' L (QuotientGroup.mk' O z)) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hzbar2]
        simp
      have hdvdL : orderOf (QuotientGroup.mk' L (QuotientGroup.mk' O z)) ∣ L.index := by
        rw [Subgroup.index]
        exact orderOf_dvd_natCard _
      have hodd : Odd (orderOf (QuotientGroup.mk' L (QuotientGroup.mk' O z))) :=
        Odd.of_dvd_nat hLodd hdvdL
      have h1 : orderOf (QuotientGroup.mk' L (QuotientGroup.mk' O z)) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff] at h1
      exact (QuotientGroup.eq_one_iff (QuotientGroup.mk' O z)).mp h1
    have hzcL : (⟨QuotientGroup.mk' O z, hzbarL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzbar_center (y : X ⧸ O)
    rcases hLiso with hne | hne
    · obtain ⟨e⟩ := hne
      have h1 : e ⟨QuotientGroup.mk' O z, hzbarL⟩ ∈
          Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
        rw [← Subgroup.map_center_eq e]
        exact ⟨_, hzcL, rfl⟩
      rw [center_PSL p k hpo hq] at h1
      have h2 : e ⟨QuotientGroup.mk' O z, hzbarL⟩ = 1 := by simpa using h1
      have h3 : (⟨QuotientGroup.mk' O z, hzbarL⟩ : ↥L) = 1 :=
        e.injective (h2.trans (map_one e).symm)
      apply hzbar_ne
      have h4 : ((⟨QuotientGroup.mk' O z, hzbarL⟩ : ↥L) : X ⧸ O) = ((1 : ↥L) : X ⧸ O) :=
        congrArg (fun w : ↥L => (w : X ⧸ O)) h3
      simpa using h4
    · obtain ⟨e⟩ := hne
      have h1 : e ⟨QuotientGroup.mk' O z, hzbarL⟩ ∈
          Subgroup.center (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) := by
        rw [← Subgroup.map_center_eq e]
        exact ⟨_, hzcL, rfl⟩
      rw [center_PGL p k hpo hq] at h1
      have h2 : e ⟨QuotientGroup.mk' O z, hzbarL⟩ = 1 := by simpa using h1
      have h3 : (⟨QuotientGroup.mk' O z, hzbarL⟩ : ↥L) = 1 :=
        e.injective (h2.trans (map_one e).symm)
      apply hzbar_ne
      have h4 : ((⟨QuotientGroup.mk' O z, hzbarL⟩ : ↥L) : X ⧸ O) = ((1 : ↥L) : X ⧸ O) :=
        congrArg (fun w : ↥L => (w : X ⧸ O)) h3
      simpa using h4

/-! ## 10. Bender 1.6 (c): `O₂(X)` a four-group and `X/(O₂(X)·O(X))` of order `3` or `6` -/

/-- **Bender 1.6 (c)**: if `O₂(X)` is a four-group and `X/(O₂(X)·O(X))` is `C₃` or `D₃`, then
`X` is solvable. -/
theorem solvable_of_d16c (X : Type) [Group X] [Finite X] (hFT : Work.GW2.FeitThompsonProp)
    (hc : d16c X) : Group.IsSolvable X := by
  classical
  obtain ⟨hV4, hquot⟩ := hc
  haveI : Group.IsSolvable ↥(Work.GW2.pCore 2 X) := by
    haveI : Group.IsNilpotent ↥(Work.GW2.pCore 2 X) :=
      (Work.CORE2A.pCore_isPGroup' (X := X) (p := 2)).isNilpotent
    exact IsNilpotent.to_isSolvable
  haveI : Group.IsSolvable ↥(Work.GW2.oddCore X) :=
    hFT ↥(Work.GW2.oddCore X) (Work.ASM.oddCore_odd X)
  have hA : Group.IsSolvable ↥(Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X) :=
    isSolvable_sup_of_normal (Work.GW2.pCore 2 X) (Work.GW2.oddCore X)
  haveI : Group.IsSolvable ↥(Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X) := hA
  have hle6 : Nat.card (X ⧸ (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)) ≤ 6 := by
    rcases hquot with ⟨hcyc, hcard⟩ | hne
    · rw [hcard]
      norm_num
    · obtain ⟨e⟩ := hne
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  haveI : Group.IsSolvable (X ⧸ (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)) :=
    isSolvable_of_card_le_six hle6
  exact Group.isSolvable_of_subgroup_quotient (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)

/-- **FStarProp** (`Work.GW2.FStarProp`): for a D-group `X`, `C_X(F*(X)) <= F*(X)`.  `h16` splits into Bender 1.6's four cases: in case (a) `C_X(F(X)) <= C_X(F_{2'}(X)) <= F_{2'}(X) <= F*(X)` directly; cases (b) and (c) make `X` solvable, so `F*(X) = F(X)` and Bender 1.2 (`he1`) applies; in case (d) (`X` has a normal quasisimple `E` with `X/E` solvable) `h5` identifies `E = layer X`, and `he1` is applied to the solvable quotient `X/E`. -/
theorem fstar (h16 : Work.GW2.D16Prop) (h5 : Work.GW2.LayerUniqueProp)
    (he1 : Work.GW2.FittingSelfCentralizingProp) : Work.GW2.FStarProp := by
  intro X _ _ hFT hSyl hD
  rcases h16 X hFT hSyl hD with ha | hb | hc | hd
  · refine le_trans (centralizer_anti ?_) (le_trans ha ?_)
    · exact le_trans (Work.DSTR.fittingPi_le' ({2}ᶜ : Set ℕ) X) le_sup_left
    · exact le_trans (Work.DSTR.fittingPi_le' ({2}ᶜ : Set ℕ) X) le_sup_left
  · exact fstar_le_of_solvable he1 X (solvable_of_central_involution X hFT hD hb)
  · exact fstar_le_of_solvable he1 X (solvable_of_d16c X hFT hc)
  · obtain ⟨E, hEn, hEq, hQsol⟩ := hd
    haveI : E.Normal := hEn
    refine solvableCentralizerFstar he1 X ?_
    haveI hCE : Group.IsSolvable ↥(Subgroup.centralizer (E : Set X)) :=
      solvable_centralizer_of_quasisimple E hEq hQsol
    have hElayer : E ≤ Work.GW2.layer X := by
      rw [Work.GW2.layer]
      exact le_sSup (s := {F : Subgroup X | F.Normal ∧ Work.GW2.IsQuasisimple F}) ⟨hEn, hEq⟩
    have hle : Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X) ≤
        Subgroup.centralizer (E : Set X) :=
      centralizer_anti (le_trans hElayer le_sup_right)
    refine Group.isSolvable_of_isSolvable_injective
      (f := ({ toFun := fun x => ⟨(x : X), hle x.2⟩
               map_one' := rfl
               map_mul' := fun a b => rfl } :
        ↥(Subgroup.centralizer ((Work.GW2.fstar X : Subgroup X) : Set X)) →*
          ↥(Subgroup.centralizer (E : Set X)))) ?_
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : ↥(Subgroup.centralizer (E : Set X)) => (z : X)) h

end Work.DSTR
