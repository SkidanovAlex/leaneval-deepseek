/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The twist of `K[N]` induced by conjugation by `t`

Let `N ⊴ H ≤ G` and `t : H` normalise `N`.  Conjugation by `t` is a group automorphism of `N`,
hence a ring automorphism `conjAlgEquiv` of the group algebra `K[N]`, and therefore generates a
`Multiplicative ℤ`-action `conjAction` on `K[N]`.  This is the twist `τ` of the *source* skew
Laurent decomposition `K[H] ≅ K[N][t^{±1}; τ]` of [JZLA20, §3.3], used in the construction of the
induction environment `Thm61Step`.

The main output is `exists_skewLaurentDecomp`, which produces a `SkewLaurentDecomp K G H N` for
this twist, together with the two formulae for `d.iso` and `d.iso.symm` on the monomials
`K[N] · t^k` which the construction of `Thm61Step` consumes.
-/
import Mathlib
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecomp_exists2
import Submission.Work.ORHughesFree.Section6.ConjAction
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecomp_exists2_iso_single

set_option autoImplicit false
set_option warn.classDefReducibility false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H} {t : H}

/-- The group automorphism `n ↦ t n t⁻¹` of `N`. -/
noncomputable def conjMulEquiv (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    N ≃* N where
  toFun n := ⟨t * (n : H) * t⁻¹, by simpa using htN 1 n⟩
  invFun n := ⟨t⁻¹ * (n : H) * t, by simpa using htN (-1) n⟩
  left_inv n := by
    refine Subtype.ext ?_
    show (t⁻¹ : H) * (t * (n : H) * t⁻¹) * t = (n : H)
    group
  right_inv n := by
    refine Subtype.ext ?_
    show (t : H) * (t⁻¹ * (n : H) * t) * t⁻¹ = (n : H)
    group
  map_mul' n m := by
    refine Subtype.ext ?_
    show (t : H) * ((n : H) * m) * t⁻¹ = (t * (n : H) * t⁻¹) * (t * (m : H) * t⁻¹)
    group

/-- The induced ring automorphism of `K[N]`. -/
noncomputable def conjAlgEquiv (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    MonoidAlgebra K N ≃+* MonoidAlgebra K N where
  toFun := MonoidAlgebra.mapDomainRingHom K (conjMulEquiv htN)
  invFun := MonoidAlgebra.mapDomainRingHom K (conjMulEquiv htN).symm
  left_inv x := by
    show MonoidAlgebra.mapDomain ((conjMulEquiv htN).symm : N → N)
      (MonoidAlgebra.mapDomain ((conjMulEquiv htN) : N → N) x) = x
    induction x using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single,
          MulEquiv.symm_apply_apply]
    | add x y ihx ihy =>
        rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add, ihx, ihy]
    | smul c x ih =>
        rw [MonoidAlgebra.mapDomain_smul, MonoidAlgebra.mapDomain_smul, ih]
  right_inv x := by
    show MonoidAlgebra.mapDomain ((conjMulEquiv htN) : N → N)
      (MonoidAlgebra.mapDomain ((conjMulEquiv htN).symm : N → N) x) = x
    induction x using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single,
          MulEquiv.apply_symm_apply]
    | add x y ihx ihy =>
        rw [MonoidAlgebra.mapDomain_add, MonoidAlgebra.mapDomain_add, ihx, ihy]
    | smul c x ih =>
        rw [MonoidAlgebra.mapDomain_smul, MonoidAlgebra.mapDomain_smul, ih]
  map_mul' x y := map_mul _ _ _
  map_add' x y := map_add _ _ _

/-- The `Multiplicative ℤ`-action on `K[N]` given by conjugation by the powers of `t`. -/
noncomputable def conjAction (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N) :=
  Work.ORHughesFree.RingEquiv.mulSemiringActionZpow (conjAlgEquiv htN)

/-- `conjAlgEquiv` on a monomial. -/
theorem conjAlgEquiv_single (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (n : N) (c : K) :
    conjAlgEquiv htN (MonoidAlgebra.single n c) =
      MonoidAlgebra.single ⟨t * (n : H) * t⁻¹, by simpa using htN 1 n⟩ c := by
  show MonoidAlgebra.mapDomain (↑(conjMulEquiv htN)) (MonoidAlgebra.single n c) = _
  rw [MonoidAlgebra.mapDomain_single]
  rfl

/-- `(conjAlgEquiv htN)⁻¹` on a monomial. -/
theorem conjAlgEquiv_symm_single (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (n : N) (c : K) :
    (conjAlgEquiv htN).symm (MonoidAlgebra.single n c) =
      MonoidAlgebra.single ⟨t⁻¹ * (n : H) * t, by simpa using htN (-1) n⟩ c := by
  show MonoidAlgebra.mapDomain (↑(conjMulEquiv htN).symm) (MonoidAlgebra.single n c) = _
  rw [MonoidAlgebra.mapDomain_single]
  rfl

/-- The group automorphism `conjMulEquiv` on powers: conjugation by `t ^ k`. -/
theorem conjMulEquiv_zpow_apply (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (k : ℤ) (n : N) :
    ((conjMulEquiv htN) ^ k) n = ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ := by
  have hbase : ∀ n : N, ((conjMulEquiv htN) ^ (0 : ℤ)) n =
      ⟨t ^ (0 : ℤ) * (n : H) * t ^ (-(0 : ℤ)), htN 0 n⟩ := by
    intro n
    rw [zpow_zero]
    refine Subtype.ext ?_
    show (n : H) = t ^ (0 : ℤ) * (n : H) * t ^ (-(0 : ℤ))
    simp
  have hsucc : ∀ (i : ℕ), (∀ n : N, ((conjMulEquiv htN) ^ (i : ℤ)) n =
      ⟨t ^ (i : ℤ) * (n : H) * t ^ (-(i : ℤ)), htN (i : ℤ) n⟩) →
      ∀ n : N, ((conjMulEquiv htN) ^ ((i : ℤ) + 1)) n =
        ⟨t ^ ((i : ℤ) + 1) * (n : H) * t ^ (-((i : ℤ) + 1)), htN ((i : ℤ) + 1) n⟩ := by
    intro i ih n
    rw [zpow_add_one]
    show ((conjMulEquiv htN) ^ (i : ℤ)) ((conjMulEquiv htN) n) = _
    have he : (conjMulEquiv htN) n = ⟨t * (n : H) * t⁻¹, by simpa using htN 1 n⟩ := rfl
    rw [he, ih]
    refine Subtype.ext ?_
    group
  have hpred : ∀ (i : ℕ), (∀ n : N, ((conjMulEquiv htN) ^ (-(i : ℤ))) n =
      ⟨t ^ (-(i : ℤ)) * (n : H) * t ^ (-(-(i : ℤ))), htN (-(i : ℤ)) n⟩) →
      ∀ n : N, ((conjMulEquiv htN) ^ (-(i : ℤ) - 1)) n =
        ⟨t ^ (-(i : ℤ) - 1) * (n : H) * t ^ (-(-(i : ℤ) - 1)), htN (-(i : ℤ) - 1) n⟩ := by
    intro i ih n
    rw [zpow_sub_one]
    show ((conjMulEquiv htN) ^ (-(i : ℤ))) ((conjMulEquiv htN)⁻¹ n) = _
    have hinv : ((conjMulEquiv htN)⁻¹) n = ⟨t⁻¹ * (n : H) * t, by simpa using htN (-1) n⟩ := rfl
    rw [hinv, ih]
    refine Subtype.ext ?_
    group
  revert n
  refine Int.induction_on k ?_ ?_ ?_
  · exact hbase
  · intro i ih
    exact hsucc i ih
  · intro i ih
    exact hpred i ih

/-- `conjAlgEquiv` on powers: conjugation by `t ^ k`. -/
theorem conjAlgEquiv_zpow_single (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (k : ℤ) (n : N) (c : K) :
    ((conjAlgEquiv htN) ^ k) (MonoidAlgebra.single n c) =
      MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ c := by
  have hbase : ∀ (n : N) (c : K), ((conjAlgEquiv htN) ^ (0 : ℤ)) (MonoidAlgebra.single n c) =
      MonoidAlgebra.single ⟨t ^ (0 : ℤ) * (n : H) * t ^ (-(0 : ℤ)), htN 0 n⟩ c := by
    intro n c
    rw [zpow_zero]
    change MonoidAlgebra.single n c =
      MonoidAlgebra.single ⟨t ^ (0 : ℤ) * (n : H) * t ^ (-(0 : ℤ)), htN 0 n⟩ c
    refine congrArg (fun z : N => MonoidAlgebra.single z c) (Subtype.ext ?_)
    show (n : H) = t ^ (0 : ℤ) * (n : H) * t ^ (-(0 : ℤ))
    simp
  have hsucc : ∀ (i : ℕ), (∀ (n : N) (c : K),
      ((conjAlgEquiv htN) ^ (i : ℤ)) (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t ^ (i : ℤ) * (n : H) * t ^ (-(i : ℤ)), htN (i : ℤ) n⟩ c) →
      ∀ (n : N) (c : K), ((conjAlgEquiv htN) ^ ((i : ℤ) + 1)) (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t ^ ((i : ℤ) + 1) * (n : H) * t ^ (-((i : ℤ) + 1)),
          htN ((i : ℤ) + 1) n⟩ c := by
    intro i ih n c
    rw [zpow_add_one]
    show ((conjAlgEquiv htN) ^ (i : ℤ)) ((conjAlgEquiv htN) (MonoidAlgebra.single n c)) = _
    have he : (conjAlgEquiv htN) (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t * (n : H) * t⁻¹, by simpa using htN 1 n⟩ c :=
      conjAlgEquiv_single htN n c
    rw [he, ih]
    refine congrArg (fun z : N => MonoidAlgebra.single z c) (Subtype.ext ?_)
    group
  have hpred : ∀ (i : ℕ), (∀ (n : N) (c : K),
      ((conjAlgEquiv htN) ^ (-(i : ℤ))) (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t ^ (-(i : ℤ)) * (n : H) * t ^ (-(-(i : ℤ))), htN (-(i : ℤ)) n⟩ c) →
      ∀ (n : N) (c : K), ((conjAlgEquiv htN) ^ (-(i : ℤ) - 1)) (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t ^ (-(i : ℤ) - 1) * (n : H) * t ^ (-(-(i : ℤ) - 1)),
          htN (-(i : ℤ) - 1) n⟩ c := by
    intro i ih n c
    rw [zpow_sub_one]
    show ((conjAlgEquiv htN) ^ (-(i : ℤ))) ((conjAlgEquiv htN)⁻¹ (MonoidAlgebra.single n c)) = _
    have hinv : (conjAlgEquiv htN)⁻¹ (MonoidAlgebra.single n c) =
        MonoidAlgebra.single ⟨t⁻¹ * (n : H) * t, by simpa using htN (-1) n⟩ c :=
      conjAlgEquiv_symm_single htN n c
    rw [hinv, ih]
    refine congrArg (fun z : N => MonoidAlgebra.single z c) (Subtype.ext ?_)
    group
  revert n c
  refine Int.induction_on k ?_ ?_ ?_
  · exact hbase
  · intro i ih
    exact hsucc i ih
  · intro i ih
    exact hpred i ih

/-- The defining formula of the twist `conjAction`. -/
theorem conjAction_hact (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    letI := conjAction (K := K) htN
    ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
      MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K) := by
  letI := conjAction (K := K) htN
  intro k n
  show (conjAlgEquiv htN ^ k) (MonoidAlgebra.single n (1 : K)) = _
  rw [conjAlgEquiv_zpow_single]

/-- `conjAlgEquiv` is `K`-linear. -/
theorem conjAlgEquiv_smul (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (c : K) (x : MonoidAlgebra K N) :
    conjAlgEquiv htN (c • x) = c • conjAlgEquiv htN x := by
  show MonoidAlgebra.mapDomain (↑(conjMulEquiv htN)) (c • x) =
    c • MonoidAlgebra.mapDomain (↑(conjMulEquiv htN)) x
  exact MonoidAlgebra.mapDomain_smul _ c x

/-- The twist `conjAction` commutes with the scalar action of `K`. -/
theorem conjAction_smul_comm (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (k : ℤ) (c : K) (x : MonoidAlgebra K N) :
    letI := conjAction (K := K) htN
    (Multiplicative.ofAdd k) • (c • x) = c • ((Multiplicative.ofAdd k) • x) := by
  letI := conjAction (K := K) htN
  set e : MonoidAlgebra K N ≃+* MonoidAlgebra K N := conjAlgEquiv htN with he
  have hesmul : ∀ y : MonoidAlgebra K N, e (c • y) = c • e y := by
    intro y
    rw [he]
    exact conjAlgEquiv_smul htN c y
  have heinv : ∀ y : MonoidAlgebra K N, e⁻¹ (c • y) = c • e⁻¹ y := by
    intro y
    apply e.injective
    rw [show e (e⁻¹ (c • y)) = c • y from by simp, hesmul,
      show e (e⁻¹ y) = y from by simp]
  show (e ^ k) (c • x) = c • ((e ^ k) x)
  exact zpow_induction_right (g := e)
    (P := fun w : MonoidAlgebra K N ≃+* MonoidAlgebra K N =>
      ∀ y : MonoidAlgebra K N, w (c • y) = c • w y)
    (fun y => by simp)
    (fun a ha y => by
      calc (a * e) (c • y) = a (e (c • y)) := by simp
        _ = a (c • e y) := by rw [hesmul]
        _ = c • a (e y) := ha (e y)
        _ = c • (a * e) y := by simp)
    (fun a ha y => by
      calc (a * e⁻¹) (c • y) = a (e⁻¹ (c • y)) := by simp
        _ = a (c • e⁻¹ y) := by rw [heinv]
        _ = c • a (e⁻¹ y) := ha (e⁻¹ y)
        _ = c • (a * e⁻¹) y := by simp) k x

/-- The twist `conjAction` and the scalar action of `K` commute. -/
theorem conjAction_smulCommClass (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N) :
    letI := conjAction (K := K) htN
    SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N) := by
  letI := conjAction (K := K) htN
  exact ⟨fun k c x => conjAction_smul_comm (K := K) htN k c x⟩

/-- **The skew Laurent decomposition of `K[H]` over `K[N]` for the twist induced by conjugation by
`t`**, with the two monomial formulae for `d.iso` and `d.iso.symm`. -/
theorem exists_skewLaurentDecomp {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G}
    {N : Subgroup H} {t : H} (hNnorm : N.Normal)
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N) :
    letI := conjAction (K := K) htN
    ∃ d : SkewLaurentDecomp K G H N,
      (∀ (a : Multiplicative ℤ) (b : MonoidAlgebra K N),
        d.iso (SkewMonoidAlgebra.single a b) = d.inclN b * HughesFree.genT K t a) ∧
      (∀ (a : Multiplicative ℤ) (b : MonoidAlgebra K N),
        d.iso.symm (d.inclN b * HughesFree.genT K t a) = SkewMonoidAlgebra.single a b) := by
  letI := conjAction (K := K) htN
  haveI := conjAction_smulCommClass (K := K) htN
  obtain ⟨d, hd⟩ := HughesFree.skewLaurentDecomp_exists2_iso_single H N t hNnorm htN hgen htinf
    (conjAction_hact (K := K) htN)
  exact ⟨d, hd, fun a b => by
    rw [← hd a b, RingEquiv.symm_apply_apply]⟩

end Work.ORHughesFree.Section6
