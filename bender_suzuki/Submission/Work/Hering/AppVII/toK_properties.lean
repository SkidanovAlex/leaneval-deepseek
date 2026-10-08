import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Hering.AppVII.toK_properties`

Let `A` be a finite group, `r` a prime with `r ∤ |A|`, `k = F̄_r`, `R = ℤ[ζ_|A|]` and
`tildeE χ = |A| • e_χ ∈ R[A]` the integral lift of `|A|` times the central primitive idempotent
`e_χ = (χ(1)/|A|) ∑_g χ(g⁻¹) g` of `ℂ[A]` attached to `χ ∈ Irr A`, with reduction
`toK hcop χ hχ = |A|⁻¹ • map (jred r |A|) (tildeE χ hχ) ∈ k[A]`.

The file proves the five standard properties of the `toK χ` (central idempotent, non-zero,
pairwise orthogonal, summing to `1`, and fixed by `single z 1` for `z` in the kernel of `χ`).

The proof has three layers.

* **The complex layer.**  In `ℂ[G]` the element `classSum χ := ∑_g χ(g⁻¹) • g` is central, and
  it acts on a simple `ℂ[G]`-module `N` by the scalar `centralChar`, whose value is computed
  here (`toK_centralChar_classSum`, `toK_classSum_acts_scalar`): `toK_cU χ := χ(1) • classSum χ` acts on `N`
  by `|G|` if `N` affords `χ`, and by `0` otherwise.  Since the chosen simple submodules of the
  regular module span `ℂ[G]`, an element of the centre of `ℂ[G]` which annihilates all of them
  is zero (`toK_eq_zero_of_central_of_forall_smul_eq_zero`); applying this to the differences gives
  the idempotent relation `toK_cU_mul_cU` and the sum relation `toK_sum_cU`.
* **The integral layer.**  `iota : ℤ[ζ_|A|] → ℂ` is injective, so `MonoidAlgebra.map iota` is
  injective (`toK_mapIota_injective`), and the images of the `tildeE χ` are the `toK_cU χ`
  (`toK_mapIota_tildeE`).  The four `R[A]` identities of `tildeE` follow by injectivity.
* **The reduction layer.**  Pushing along `jred : R → k` and scaling by `|A|⁻¹` gives the five
  statements; non-vanishing is read off from the coefficient of `1`, which is `|A|⁻¹ χ(1)²`, and
  `χ(1) ∣ |A|` is invertible in `k` since `r ∤ |A|`.
-/

noncomputable section

open Classical

open scoped BigOperators

namespace Work.Hering.AppVII

/-! ## Part 1 — the complex group algebra

We work in `ℂ[G]` for an arbitrary finite group `G`.  The element
`classSum χ = ∑_g χ(g⁻¹) • single g 1` is central for `χ ∈ Irr G`, and its `χ(1)`-multiple
`toK_cU χ` acts on a simple module affording `χ'` by `|G|` if `χ' = χ` and by `0` otherwise. -/

section ComplexLayer

variable {G : Type*} [Group G] [Fintype G]

/-- The element `toK_cU χ = χ(1) • classSum χ` of the complex group algebra.  Its image in `k[A]`
is the reduction of `tildeE χ`, and its `|A|⁻¹`-multiple is the central idempotent `e_χ`. -/
noncomputable def toK_cU (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  (Work.CharCore.irrDeg χ : ℂ) • Work.CharCore.classSum χ

/-- `toK_cU χ` is central. -/
theorem toK_cU_central {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) :
    toK_cU χ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  Subalgebra.smul_mem _
    (Subalgebra.mem_center_iff.mpr fun a =>
      (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm)
    (Work.CharCore.irrDeg χ : ℂ)

/-- **The central character of the class sum `classSum χ`.**  On a simple module `N` of degree
`d`, `classSum χ` acts by the scalar `centralChar`; this scalar times `d` is the trace of the
action, i.e. `∑_g χ(g⁻¹) χ_N(g) = |G| ⟨χ_N, χ⟩`, which is `|G|` if `χ_N = χ` and `0` else. -/
theorem toK_centralChar_classSum (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G)
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N) :
    Work.CharCore.centralChar N hN
        ⟨Work.CharCore.classSum χ, Subalgebra.mem_center_iff.mpr fun a =>
          (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm⟩ *
      (Module.finrank ℂ N : ℂ)
      = (Nat.card G : ℂ) *
        (if (Work.CharCore.submoduleRep N).character = χ then 1 else 0) := by
  have hcent : Work.CharCore.classSum χ ∈ Subalgebra.center ℂ (Work.CharCore.groupAlgebra G) :=
    Subalgebra.mem_center_iff.mpr fun a =>
      (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm
  -- the scalar by which `classSum χ` acts on `N` times the degree is the trace
  have htr1 : Work.CharCore.centralChar N hN ⟨Work.CharCore.classSum χ, hcent⟩ *
      (Module.finrank ℂ N : ℂ)
      = LinearMap.trace ℂ N (Algebra.lsmul ℂ (A := Work.CharCore.groupAlgebra G) ℂ N
          (Work.CharCore.classSum χ)) := by
    have h : (Algebra.lsmul ℂ (A := Work.CharCore.groupAlgebra G) ℂ N)
        (Work.CharCore.classSum χ)
        = (Work.CharCore.centralChar N hN ⟨Work.CharCore.classSum χ, hcent⟩) •
            (1 : N →ₗ[ℂ] N) := by
      refine LinearMap.ext fun n => ?_
      rw [Algebra.lsmul_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact Work.CharCore.centralChar_spec N hN ⟨Work.CharCore.classSum χ, hcent⟩ n
    rw [h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [htr1, Work.CharCore.classSum, map_sum, map_sum]
  have hstep : ∀ g : G, LinearMap.trace ℂ N
      (Algebra.lsmul ℂ (A := Work.CharCore.groupAlgebra G) ℂ N
        (χ (g⁻¹) • MonoidAlgebra.single g (1 : ℂ))) =
      χ (g⁻¹) * (Work.CharCore.submoduleRep N).character g := by
    intro g
    rw [map_smul, map_smul, smul_eq_mul]
    rfl
  rw [Finset.sum_congr rfl (fun g _ => hstep g)]
  have hχN : (Work.CharCore.submoduleRep N).character ∈ Work.CharCore.Irr G :=
    Work.CharCore.irreducible_character_mem_Irr _
      (Work.CharCore.isIrreducible_submoduleRep N hN)
  have hchar : (∑ g : G, χ (g⁻¹) * (Work.CharCore.submoduleRep N).character g)
      = (Nat.card G : ℂ) * Work.CharCore.cfInner (Work.CharCore.submoduleRep N).character χ := by
    rw [Work.CharCore.cfInner_apply, Fintype.card_eq_nat_card]
    have hcard : ((Nat.card G : ℕ) : ℂ) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
    rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Work.CharCore.star_Irr χ hχ g, mul_comm]
  rw [hchar, Work.CharCore.irr_orthonormal _ _ hχN hχ, mul_ite, mul_one, mul_zero]

/-- The scalar by which `toK_cU χ` acts on a simple module `N`: `|G|` if `N` affords `χ`, else `0`. -/
theorem toK_classSum_acts_scalar (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G)
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N) :
    (Work.CharCore.irrDeg χ : ℂ) * Work.CharCore.centralChar N hN
        ⟨Work.CharCore.classSum χ, Subalgebra.mem_center_iff.mpr fun a =>
          (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm⟩
      = if (Work.CharCore.submoduleRep N).character = χ then (Nat.card G : ℂ) else 0 := by
  have hmain := toK_centralChar_classSum χ hχ N hN
  have hnt : Nontrivial N := IsSimpleModule.nontrivial (Work.CharCore.groupAlgebra G) N
  have hd : (Module.finrank ℂ N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos_iff.mpr hnt).ne'
  by_cases hcase : (Work.CharCore.submoduleRep N).character = χ
  · have hmain' := hmain
    rw [if_pos hcase] at hmain'
    simp only [mul_one] at hmain'
    rw [if_pos hcase]
    have hdeg : (Module.finrank ℂ N : ℂ) = (Work.CharCore.irrDeg χ : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hχ, ← hcase]
      exact (Representation.char_one (Work.CharCore.submoduleRep N)).symm
    have key : (Work.CharCore.irrDeg χ : ℂ) * Work.CharCore.centralChar N hN
          ⟨Work.CharCore.classSum χ, Subalgebra.mem_center_iff.mpr fun a =>
            (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm⟩ *
          (Work.CharCore.irrDeg χ : ℂ)
        = (Nat.card G : ℂ) * (Work.CharCore.irrDeg χ : ℂ) := by
      rw [← hdeg, mul_assoc, hmain', mul_comm]
    exact mul_right_cancel₀ (Work.CharCore.irrDeg_ne_zero hχ) key
  · have hmain' := hmain
    rw [if_neg hcase] at hmain'
    simp only [mul_zero] at hmain'
    rw [if_neg hcase]
    rw [(mul_eq_zero.mp hmain').resolve_right hd, mul_zero]

/-- `toK_cU χ` acts on a simple module `N` by the scalar `|G|` if `N` affords `χ` and by `0` else. -/
theorem toK_cU_smul_eq_ite (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G)
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N) (x : N) :
    toK_cU χ • x =
      (if (Work.CharCore.submoduleRep N).character = χ then (Nat.card G : ℂ) else 0) • x := by
  have hspec := Work.CharCore.centralChar_spec N hN
    ⟨Work.CharCore.classSum χ, Subalgebra.mem_center_iff.mpr fun a =>
      (Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a).symm⟩ x
  rw [toK_cU, smul_assoc, hspec, smul_smul, toK_classSum_acts_scalar χ hχ N hN]

/-- A central element of `ℂ[G]` annihilating every chosen simple submodule of the regular module
is zero. -/
theorem toK_eq_zero_of_central_of_forall_smul_eq_zero {y : MonoidAlgebra ℂ G}
    (hy : y ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (h : ∀ (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
        N ∈ Work.CharCore.irrSubmodules G → ∀ x : N, y • x = 0) : y = 0 := by
  let K : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {w | y * w = 0}
      add_mem' := by
        intro a b ha hb
        show y * (a + b) = 0
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by
        show y * 0 = 0
        simp
      smul_mem' := by
        intro a b hb
        show y * (a * b) = 0
        rw [← mul_assoc, (Subalgebra.mem_center_iff.mp hy a).symm, mul_assoc, hb, mul_zero] }
  have hle : sSup ((Work.CharCore.irrSubmodules G :
      Finset (Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) : Set _) ≤ K := by
    refine sSup_le fun N hN w hw => ?_
    show y * w = 0
    exact congrArg Subtype.val (h N hN ⟨w, hw⟩)
  have htop : K = ⊤ := top_unique (by rw [← Work.CharCore.sSup_irrSubmodules G]; exact hle)
  have hone : y * (1 : MonoidAlgebra ℂ G) = 0 := by
    have : (1 : MonoidAlgebra ℂ G) ∈ K := by rw [htop]; exact Submodule.mem_top
    exact this
  simpa using hone

/-- **The idempotent relation**: `toK_cU χ * toK_cU ψ = |G| • toK_cU ψ` if `χ = ψ` and `0` otherwise. -/
theorem toK_cU_mul_cU (χ ψ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G) (hψ : ψ ∈ Work.CharCore.Irr G) :
    toK_cU χ * toK_cU ψ = if χ = ψ then (Nat.card G : ℂ) • toK_cU ψ else 0 := by
  set y : MonoidAlgebra ℂ G :=
    toK_cU χ * toK_cU ψ - (if χ = ψ then (Nat.card G : ℂ) • toK_cU ψ else 0) with hydef
  have hy : y ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
    rw [hydef]
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (toK_cU_central hχ) (toK_cU_central hψ)) ?_
    by_cases h : χ = ψ
    · rw [if_pos h]
      exact Subalgebra.smul_mem _ (toK_cU_central hψ) (Nat.card G : ℂ)
    · rw [if_neg h]
      exact Subalgebra.zero_mem _
  have hann : ∀ (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
      N ∈ Work.CharCore.irrSubmodules G → ∀ x : N, y • x = 0 := by
    intro N hN x
    haveI hsimp : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
      Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
    -- the scalar identity behind the annihilation
    have hscal :
        ((if (Work.CharCore.submoduleRep N).character = χ then (Nat.card G : ℂ) else 0) -
          (if χ = ψ then (Nat.card G : ℂ) else 0)) *
        (if (Work.CharCore.submoduleRep N).character = ψ then (Nat.card G : ℂ) else 0) = 0 := by
      by_cases h1 : (Work.CharCore.submoduleRep N).character = χ
      · by_cases h2 : (Work.CharCore.submoduleRep N).character = ψ
        · rw [if_pos h1, if_pos h2, if_pos (h1.symm.trans h2), sub_self, zero_mul]
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_sub]
        by_cases hχψ : χ = ψ
        · rw [if_pos hχψ,
            if_neg (fun h : (Work.CharCore.submoduleRep N).character = ψ =>
              h1 (h.trans hχψ.symm)), mul_zero]
        · rw [if_neg hχψ, neg_zero, zero_mul]
    have h1 : (toK_cU χ * toK_cU ψ) • x =
        ((if (Work.CharCore.submoduleRep N).character = χ then (Nat.card G : ℂ) else 0) *
          (if (Work.CharCore.submoduleRep N).character = ψ then
            (Nat.card G : ℂ) else 0)) • x := by
      rw [mul_smul (toK_cU χ) (toK_cU ψ) x, toK_cU_smul_eq_ite χ hχ N hsimp (toK_cU ψ • x),
        toK_cU_smul_eq_ite ψ hψ N hsimp x, smul_smul]
    have h2 : (if χ = ψ then (Nat.card G : ℂ) • toK_cU ψ else 0) • x =
        ((if χ = ψ then (Nat.card G : ℂ) else 0) *
          (if (Work.CharCore.submoduleRep N).character = ψ then
            (Nat.card G : ℂ) else 0)) • x := by
      by_cases h : χ = ψ
      · rw [if_pos h, if_pos h, smul_assoc (Nat.card G : ℂ) (toK_cU ψ) x,
          toK_cU_smul_eq_ite ψ hψ N hsimp x, smul_smul]
      · rw [if_neg h, if_neg h, zero_smul, zero_mul, zero_smul]
    rw [hydef, sub_smul (toK_cU χ * toK_cU ψ) (if χ = ψ then (Nat.card G : ℂ) • toK_cU ψ else 0) x,
      h1, h2, ← sub_smul _ _ x, ← sub_mul, hscal, zero_smul]
  have hzero := toK_eq_zero_of_central_of_forall_smul_eq_zero hy hann
  rw [hydef] at hzero
  exact sub_eq_zero.mp hzero

/-- **The sum relation**: the `toK_cU χ` sum to `|G| • 1` (the `|G|`-multiple of the identity of the
group algebra, i.e. the regular character). -/
theorem toK_sum_cU : Finset.sum (Work.CharCore.Irr G) (fun χ => toK_cU χ) =
    (Nat.card G : ℂ) • (1 : MonoidAlgebra ℂ G) := by
  set y : MonoidAlgebra ℂ G :=
    Finset.sum (Work.CharCore.Irr G) (fun χ => toK_cU χ) - (Nat.card G : ℂ) • 1 with hydef
  have hy : y ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
    rw [hydef]
    exact Subalgebra.sub_mem _
      (Subalgebra.sum_mem _ fun χ hχ => toK_cU_central hχ) 
      (Subalgebra.smul_mem _ (Subalgebra.one_mem _) (Nat.card G : ℂ))
  have hann : ∀ (N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)),
      N ∈ Work.CharCore.irrSubmodules G → ∀ x : N, y • x = 0 := by
    intro N hN x
    haveI hsimp : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
      Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
    have hχN : (Work.CharCore.submoduleRep N).character ∈ Work.CharCore.Irr G :=
      Work.CharCore.irreducible_character_mem_Irr _
        (Work.CharCore.isIrreducible_submoduleRep N hsimp)
    have hsum : (∑ χ ∈ Work.CharCore.Irr G,
        (if (Work.CharCore.submoduleRep N).character = χ then (Nat.card G : ℂ) else 0))
        = (Nat.card G : ℂ) := by
      rw [Finset.sum_eq_single (Work.CharCore.submoduleRep N).character]
      · simp
      · intro b _ hne
        rw [if_neg (Ne.symm hne)]
      · intro hmem
        exact absurd hχN hmem
    have h2 : ((Nat.card G : ℂ) • (1 : MonoidAlgebra ℂ G)) • x = (Nat.card G : ℂ) • x := by
      rw [smul_assoc (Nat.card G : ℂ) (1 : MonoidAlgebra ℂ G) x,
        one_smul (MonoidAlgebra ℂ G) x]
    have h1 : (Finset.sum (Work.CharCore.Irr G) (fun χ => toK_cU χ)) • x =
        (∑ χ ∈ Work.CharCore.Irr G,
          (if (Work.CharCore.submoduleRep N).character = χ then
            (Nat.card G : ℂ) else 0)) • x := by
      rw [Finset.sum_smul,
        Finset.sum_congr rfl (fun χ hχ => toK_cU_smul_eq_ite χ hχ N hsimp x), ← Finset.sum_smul]
    rw [hydef,
      sub_smul (Finset.sum (Work.CharCore.Irr G) (fun χ => toK_cU χ))
        ((Nat.card G : ℂ) • (1 : MonoidAlgebra ℂ G)) x,
      h1, h2, ← sub_smul _ _ x, hsum, sub_self, zero_smul]
  have hzero := toK_eq_zero_of_central_of_forall_smul_eq_zero hy hann
  rw [hydef] at hzero
  exact sub_eq_zero.mp hzero

/-- Right multiplication by `single z 1` fixes `classSum χ` when `χ z = χ 1`. -/
theorem toK_classSum_mul_single_charKernel (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G) (z : G)
    (hz : χ z = χ 1) :
    Work.CharCore.classSum χ * MonoidAlgebra.single z (1 : ℂ) = Work.CharCore.classSum χ := by
  have hzg : ∀ y : G, χ (z * y) = χ y := by
    obtain ⟨N, hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
    haveI hsimp : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
      Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
    have hρ : (Work.CharCore.submoduleRep N).IsIrreducible :=
      Work.CharCore.isIrreducible_submoduleRep N hsimp
    have hz' : (Work.CharCore.submoduleRep N).character z =
        (Work.CharCore.submoduleRep N).character 1 := by
      rw [hNχ]; exact hz
    have hz1 : Work.CharCore.submoduleRep N z = 1 :=
      Work.CharCore.eq_one_of_character_eq_degree _ hρ z hz'
    intro y
    rw [← hNχ]
    show LinearMap.trace ℂ N (Work.CharCore.submoduleRep N (z * y)) =
      LinearMap.trace ℂ N (Work.CharCore.submoduleRep N y)
    rw [map_mul, hz1, one_mul]
  rw [Work.CharCore.classSum_mul_single]
  rw [← Equiv.sum_comp (Equiv.mulRight z⁻¹)
    (fun g : G => χ (g⁻¹) • MonoidAlgebra.single (g * z) (1 : ℂ))]
  simp only [Equiv.coe_mulRight]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : (g * z⁻¹) * z = g := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have h2 : (g * z⁻¹)⁻¹ = z * g⁻¹ := by rw [mul_inv_rev, inv_inv]
  rw [h1, h2, hzg g⁻¹]

end ComplexLayer

/-! ## Part 2 — the integral group algebra `ℤ[ζ_|A|][A]`

`toK_mapIota` is the coefficientwise extension of `iota : ℤ[ζ_|A|] → ℂ` to group algebras.  It is
injective, and it carries `tildeE χ` to `toK_cU χ`, so the identities of Part 1 transfer to
`ℤ[ζ_|A|][A]`. -/

section IntegralLayer

variable {A : Type*} [Group A] [Fintype A]

/-- The extension of `iota : ℤ[ζ_|A|] → ℂ` to group algebras, coefficientwise. -/
noncomputable abbrev toK_mapIota :
    MonoidAlgebra (CycloRing (Nat.card A)) A →+* MonoidAlgebra ℂ A :=
  MonoidAlgebra.mapRingHom A (iota (Nat.card A))

theorem toK_mapIota_single_one (g : A) :
    toK_mapIota (MonoidAlgebra.single g (1 : CycloRing (Nat.card A))) =
      MonoidAlgebra.single g (1 : ℂ) := by
  rw [MonoidAlgebra.mapRingHom_single, map_one]

theorem toK_mapIota_smul (c : CycloRing (Nat.card A))
    (x : MonoidAlgebra (CycloRing (Nat.card A)) A) :
    toK_mapIota (c • x) = iota (Nat.card A) c • toK_mapIota x := by
  have h := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_algebraMap (M := A) (iota (Nat.card A))) c
  simp only [RingHom.comp_apply] at h
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]

theorem toK_mapIota_injective : Function.Injective (toK_mapIota (A := A)) := by
  show Function.Injective (MonoidAlgebra.map
    (↑(iota (Nat.card A)) : CycloRing (Nat.card A) →+ ℂ))
  exact MonoidAlgebra.map_injective _ iota_injective

theorem toK_mapIota_tildeE (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    toK_mapIota (tildeE χ hχ) = toK_cU χ := by
  show toK_mapIota (tildeE χ hχ) =
    (Work.CharCore.irrDeg χ : ℂ) • Work.CharCore.classSum χ
  rw [tildeE, toK_mapIota_smul, map_natCast,
    map_sum toK_mapIota
      (fun g : A => charLift χ hχ (g⁻¹) •
        MonoidAlgebra.single g (1 : CycloRing (Nat.card A))) Finset.univ,
    Work.CharCore.classSum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [toK_mapIota_smul, toK_mapIota_single_one, iota_charLift]

/-- The square relation for the integral lifts. -/
theorem toK_tildeE_mul_self_aux (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    tildeE χ hχ * tildeE χ hχ =
      (Nat.card A : CycloRing (Nat.card A)) • tildeE χ hχ := by
  refine toK_mapIota_injective ?_
  rw [map_mul, toK_mapIota_smul, map_natCast, toK_mapIota_tildeE χ hχ,
    toK_cU_mul_cU χ χ hχ hχ, if_pos rfl]

/-- Orthogonality of the integral lifts attached to distinct characters. -/
theorem toK_tildeE_mul_eq_zero_aux {χ χ' : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A)
    (hχ' : χ' ∈ Work.CharCore.Irr A) (hne : χ ≠ χ') :
    tildeE χ hχ * tildeE χ' hχ' = 0 := by
  refine toK_mapIota_injective ?_
  rw [map_mul, toK_mapIota_tildeE χ hχ, toK_mapIota_tildeE χ' hχ', map_zero,
    toK_cU_mul_cU χ χ' hχ hχ', if_neg hne]

/-- The integral lifts sum to `|A|`. -/
theorem toK_tildeE_sum_aux :
    Finset.sum (Work.CharCore.Irr A).attach (fun x => tildeE x.1 x.2) =
      (Nat.card A : CycloRing (Nat.card A)) •
        (1 : MonoidAlgebra (CycloRing (Nat.card A)) A) := by
  refine toK_mapIota_injective ?_
  rw [map_sum toK_mapIota (fun x : {χ // χ ∈ Work.CharCore.Irr A} => tildeE x.1 x.2)
      (Work.CharCore.Irr A).attach,
    Finset.sum_congr rfl (fun x _ => toK_mapIota_tildeE x.1 x.2),
    Finset.sum_attach (Work.CharCore.Irr A) (fun χ => toK_cU χ),
    toK_sum_cU, toK_mapIota_smul, map_natCast, map_one]

/-- Centrality of the integral lifts. -/
theorem toK_tildeE_central_aux (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
    (x : MonoidAlgebra (CycloRing (Nat.card A)) A) :
    x * tildeE χ hχ = tildeE χ hχ * x := by
  refine toK_mapIota_injective ?_
  rw [map_mul, map_mul, toK_mapIota_tildeE χ hχ]
  exact Subalgebra.mem_center_iff.mp (toK_cU_central hχ) (toK_mapIota x)

/-- Right multiplication by `single z 1` fixes `tildeE χ` when `χ z = χ 1`. -/
theorem toK_tildeE_mul_single_aux (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A)
    (hz : χ z = χ 1) :
    tildeE χ hχ * MonoidAlgebra.single z (1 : CycloRing (Nat.card A)) = tildeE χ hχ := by
  refine toK_mapIota_injective ?_
  rw [map_mul, toK_mapIota_tildeE χ hχ, toK_mapIota_single_one]
  show toK_cU χ * MonoidAlgebra.single z (1 : ℂ) = toK_cU χ
  rw [toK_cU, smul_mul_assoc, toK_classSum_mul_single_charKernel χ hχ z hz]

/-- The coefficient of `single m 1` in a sum of scalar multiples of basis elements. -/
theorem toK_coeff_sum_smul_single {G R : Type*} [Group G] [Fintype G] [Semiring R]
    (c : G → R) (m : G) :
    (∑ g : G, c g • MonoidAlgebra.single g (1 : R)).coeff m = c m := by
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single m]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · intro b _ hb
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (Ne.symm hb), smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

/-- The coefficient of `single 1 1` in `tildeE χ` is `χ(1)²`. -/
theorem toK_coeff_one_tildeE (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    (tildeE χ hχ).coeff 1 = (((Work.CharCore.irrDeg χ : ℕ)) : CycloRing (Nat.card A)) ^ 2 := by
  have hc : charLift χ hχ 1 = (((Work.CharCore.irrDeg χ : ℕ)) : CycloRing (Nat.card A)) := by
    apply iota_injective
    rw [iota_charLift, map_natCast, Work.CharCore.irrDeg_spec hχ]
  rw [tildeE, MonoidAlgebra.coeff_smul_apply,
    toK_coeff_sum_smul_single (fun g : A => charLift χ hχ (g⁻¹)) 1, inv_one, hc,
    smul_eq_mul, ← pow_two]

end IntegralLayer

/-! ## Part 3 — the reduction `R[A] → k[A]`

Pushing the identities of Part 2 along `jred r |A|`, and scaling by `|A|⁻¹ ∈ k`, gives the five
properties of the `toK χ`; non-vanishing is read off from the coefficient of `single 1 1`. -/

section ReductionLayer

variable {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]

/-- The coefficientwise reduction `ℤ[ζ_|A|][A] → k[A]` induced by `jred r |A|`. -/
noncomputable abbrev toK_mapJred (hcop : Nat.Coprime r (Nat.card A)) :
    MonoidAlgebra (CycloRing (Nat.card A)) A →+* MonoidAlgebra (BrauerField r) A :=
  MonoidAlgebra.mapRingHom A (jred r (Nat.card A) (not_dvd_card hcop))

theorem toK_mapJred_single_one (hcop : Nat.Coprime r (Nat.card A)) (g : A) :
    toK_mapJred hcop (MonoidAlgebra.single g (1 : CycloRing (Nat.card A))) =
      MonoidAlgebra.single g (1 : BrauerField r) := by
  rw [MonoidAlgebra.mapRingHom_single, map_one]

theorem toK_mapJred_smul (hcop : Nat.Coprime r (Nat.card A)) (c : CycloRing (Nat.card A))
    (x : MonoidAlgebra (CycloRing (Nat.card A)) A) :
    toK_mapJred hcop (c • x) = jred r (Nat.card A) (not_dvd_card hcop) c • toK_mapJred hcop x := by
  have h := RingHom.congr_fun (MonoidAlgebra.mapRingHom_comp_algebraMap (M := A)
    (jred r (Nat.card A) (not_dvd_card hcop))) c
  simp only [RingHom.comp_apply] at h
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h]

/-- `toK` is `|A|⁻¹` times the reduction of `tildeE`. -/
theorem toK_eq_mapJred (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    toK hcop χ hχ = (Nat.card A : BrauerField r)⁻¹ • toK_mapJred hcop (tildeE χ hχ) := rfl

theorem toK_mapJred_tildeE_mul_self (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    toK_mapJred hcop (tildeE χ hχ) * toK_mapJred hcop (tildeE χ hχ) =
      (Nat.card A : BrauerField r) • toK_mapJred hcop (tildeE χ hχ) := by
  rw [← map_mul, toK_tildeE_mul_self_aux χ hχ, toK_mapJred_smul, map_natCast]

theorem toK_mapJred_tildeE_mul_eq_zero (hcop : Nat.Coprime r (Nat.card A)) {χ χ' : A → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A) (hne : χ ≠ χ') :
    toK_mapJred hcop (tildeE χ hχ) * toK_mapJred hcop (tildeE χ' hχ') = 0 := by
  rw [← map_mul, toK_tildeE_mul_eq_zero_aux hχ hχ' hne, map_zero]

theorem toK_mapJred_tildeE_sum (hcop : Nat.Coprime r (Nat.card A)) :
    Finset.sum (Work.CharCore.Irr A).attach (fun x => toK_mapJred hcop (tildeE x.1 x.2)) =
      (Nat.card A : BrauerField r) •
        (1 : MonoidAlgebra (BrauerField r) A) := by
  rw [← map_sum (toK_mapJred hcop) (fun x : {χ // χ ∈ Work.CharCore.Irr A} => tildeE x.1 x.2)
      (Work.CharCore.Irr A).attach, toK_tildeE_sum_aux, toK_mapJred_smul, map_natCast, map_one]

theorem toK_mapJred_tildeE_central (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    ∀ x : MonoidAlgebra (BrauerField r) A,
      x * toK_mapJred hcop (tildeE χ hχ) = toK_mapJred hcop (tildeE χ hχ) * x := by
  have hsingle : ∀ m : A,
      MonoidAlgebra.single m (1 : BrauerField r) * toK_mapJred hcop (tildeE χ hχ) =
        toK_mapJred hcop (tildeE χ hχ) * MonoidAlgebra.single m (1 : BrauerField r) := by
    intro m
    have h := congrArg (toK_mapJred hcop)
      (toK_tildeE_central_aux χ hχ (MonoidAlgebra.single m (1 : CycloRing (Nat.card A))))
    rwa [map_mul, map_mul, toK_mapJred_single_one hcop m] at h
  intro x
  induction x using MonoidAlgebra.induction_on with
  | of m => simpa using hsingle m
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | smul c a ha =>
      rw [smul_mul_assoc c a (toK_mapJred hcop (tildeE χ hχ)),
        mul_smul_comm c (toK_mapJred hcop (tildeE χ hχ)) a, ha]

theorem toK_mapJred_tildeE_mul_single (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) (z : A) (hz : χ z = χ 1) :
    toK_mapJred hcop (tildeE χ hχ) * MonoidAlgebra.single z (1 : BrauerField r) =
      toK_mapJred hcop (tildeE χ hχ) := by
  rw [← toK_mapJred_single_one hcop z, ← map_mul, toK_tildeE_mul_single_aux χ hχ z hz]

theorem toK_mapJred_tildeE_ne_zero (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    toK_mapJred hcop (tildeE χ hχ) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun x : MonoidAlgebra (BrauerField r) A => x.coeff 1) hzero
  rw [MonoidAlgebra.coeff_mapRingHom, toK_coeff_one_tildeE χ hχ, MonoidAlgebra.coeff_zero,
    map_pow, map_natCast] at hcoeff
  have hd : (((Work.CharCore.irrDeg χ : ℕ)) : BrauerField r) ≠ 0 := by
    intro h
    exact not_dvd_card hcop
      (((CharP.cast_eq_zero_iff (BrauerField r) r (Work.CharCore.irrDeg χ)).mp h).trans
        (Work.CharCore.irr_degree_dvd_card hχ))
  exact (pow_ne_zero 2 hd) hcoeff

/-- Scalar multiplication by `M` and the transfer of its algebraic properties. -/
theorem toK_smul_mul_self_of {k R : Type*} [Field k] [Ring R] [Algebra k R] {M : R} {n : k}
    (hn : n ≠ 0) (hM : M * M = n • M) : (n⁻¹ • M) * (n⁻¹ • M) = n⁻¹ • M := by
  calc (n⁻¹ • M) * (n⁻¹ • M) = n⁻¹ • (M * (n⁻¹ • M)) := smul_mul_assoc n⁻¹ M (n⁻¹ • M)
    _ = n⁻¹ • (n⁻¹ • (M * M)) := by rw [mul_smul_comm n⁻¹ M M]
    _ = (n⁻¹ * n⁻¹) • (M * M) := smul_smul n⁻¹ n⁻¹ (M * M)
    _ = (n⁻¹ * n⁻¹) • (n • M) := by rw [hM]
    _ = ((n⁻¹ * n⁻¹) * n) • M := smul_smul (n⁻¹ * n⁻¹) n M
    _ = n⁻¹ • M := by rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]

theorem toK_smul_central {k R : Type*} [Field k] [Ring R] [Algebra k R] {M : R}
    (hM : ∀ x : R, x * M = M * x) (c : k) : ∀ x : R, x * (c • M) = (c • M) * x := by
  intro x
  rw [mul_smul_comm c x M, smul_mul_assoc c M x, hM x]

theorem toK_smul_mul_smul_eq_zero {k R : Type*} [Field k] [Ring R] [Algebra k R]
    {M M' : R} (c : k) (h : M * M' = 0) : (c • M) * (c • M') = 0 := by
  rw [smul_mul_assoc c M (c • M'), mul_smul_comm c M M', smul_smul, h, smul_zero]

theorem toK_smul_mul_single {k R : Type*} [Field k] [Ring R] [Algebra k R]
    {M s : R} (c : k) (h : M * s = M) : (c • M) * s = c • M := by
  rw [smul_mul_assoc, h]

end ReductionLayer

/-- **The five properties of the Brauer-lifted central idempotents.**

For a finite group `A`, a prime `r` coprime to `|A|`, and `k = F̄_r`, the elements
`toK hcop χ hχ ∈ k[A]` are central idempotents, non-zero, pairwise orthogonal, sum to `1`, and
are fixed by right multiplication by `single z 1` for `z` in the kernel of `χ`. -/
theorem toK_properties {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A)) :
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
        Work.Hering.AppVII.IsCentralIdempotent (Work.Hering.AppVII.toK hcop χ hχ)) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A), Work.Hering.AppVII.toK hcop χ hχ ≠ 0) ∧
    (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A),
        χ ≠ χ' → Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0) ∧
    (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
        Work.Hering.AppVII.toK hcop χ hχ *
          MonoidAlgebra.single z (1 : Work.Hering.AppVII.BrauerField r) =
        Work.Hering.AppVII.toK hcop χ hχ) := by
  classical
  have hn : (((Nat.card A : ℕ)) : Work.Hering.AppVII.BrauerField r) ≠ 0 := fun h =>
    not_dvd_card hcop
      ((CharP.cast_eq_zero_iff (Work.Hering.AppVII.BrauerField r) r (Nat.card A)).mp h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    refine ⟨?_, ?_⟩
    · rw [toK_eq_mapJred hcop χ hχ]
      exact toK_smul_mul_self_of hn (toK_mapJred_tildeE_mul_self hcop χ hχ)
    · intro x
      rw [toK_eq_mapJred hcop χ hχ]
      exact toK_smul_central (toK_mapJred_tildeE_central hcop χ hχ) _ x
  · intro χ hχ hzero
    rw [toK_eq_mapJred hcop χ hχ] at hzero
    exact toK_mapJred_tildeE_ne_zero hcop χ hχ
      ((smul_eq_zero.mp hzero).resolve_left (inv_ne_zero hn))
  · intro χ χ' hχ hχ' hne
    rw [toK_eq_mapJred hcop χ hχ, toK_eq_mapJred hcop χ' hχ']
    exact toK_smul_mul_smul_eq_zero _ (toK_mapJred_tildeE_mul_eq_zero hcop hχ hχ' hne)
  · have h1 : Finset.sum (Work.CharCore.Irr A).attach
          (fun x => Work.Hering.AppVII.toK hcop x.1 x.2)
        = ((Nat.card A : ℕ) : Work.Hering.AppVII.BrauerField r)⁻¹ •
          Finset.sum (Work.CharCore.Irr A).attach
            (fun x => toK_mapJred hcop (tildeE x.1 x.2)) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun x _ => toK_eq_mapJred hcop x.1 x.2)
    rw [h1, toK_mapJred_tildeE_sum hcop, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · intro χ hχ z hz
    rw [toK_eq_mapJred hcop χ hχ]
    exact toK_smul_mul_single _ (toK_mapJred_tildeE_mul_single hcop χ hχ z hz)

end Work.Hering.AppVII
