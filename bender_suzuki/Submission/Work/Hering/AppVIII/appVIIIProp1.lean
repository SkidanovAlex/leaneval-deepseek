/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Higman.Family
import Submission.Work.Hering.AppVIII.frobPowOfFourth
import Submission.Work.Hering.AppVIII.SemiLinAux
import Submission.Work.Hering.AppVIII.FrobField
import Submission.Work.Hering.AppVIII.FrobBasis
import Submission.Work.Hering.AppVIII.supportSingleton
import Submission.Work.Hering.AppVIII.typeACore
import Submission.Work.Hering.AppVIII.galoisFieldZero
import Submission.Work.Higman.coeff_vanishing_of_scale

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix VIII, Proposition 1: `Aut(A(n,φ))` is solvable

Let `K = GF(2ⁿ)` and let `φ` be a field automorphism of `K` with `φ⁴ ≠ 1`.  We show that the
automorphism group of the Higman group `A(n,φ)` — the two-step group on `K × K` with law
`(x,z) * (y,w) = (x + y, z + w + x·φ(y))` — is solvable.

The argument follows Peterfalvi I, App. VIII, Prop. 1 (p. 224):

* every `α ∈ Aut(A(n,φ))` induces a pair of additive maps `f = f_α` on `A/Z = K` and
  `g = g_α` on `Z = {(0,z)} ≅ K` satisfying `g(x·φ(x)) = f(x)·φ(f(x))` for all `x`;
* writing `φ(x) = x ^ (2 ^ s)` with `s < n` (`φ⁴ ≠ 1` means `n ∤ 4s`) and expanding `f`, `g` in
  Frobenius powers `f x = ∑ᵢ λᵢ x ^ (2 ^ i)`, `g x = ∑ᵢ μᵢ x ^ (2 ^ i)`, the displayed identity
  yields the coefficient relations `λᵢ λ_{i-s}^{2^s} = 0` and
  `λᵢ λ_{j-s}^{2^s} + λⱼ λ_{i-s}^{2^s} = 0` for `i - j ≢ 0, ±s (mod n)`, whence
  `f x = λ x ^ (2 ^ i)` and `g x = λ φ(λ) x ^ (2 ^ i)` (`λ ≠ 0`, `i < n`);
* consequently `α ↦ f_α` is a homomorphism whose kernel is abelian (its elements are the maps
  `(x,z) ↦ (x, z + h x)` with `h` additive) and whose image lies in the solvable semilinear group
  `Γ = {x ↦ a·Φ^i x} = gammaLin K`, so `Aut(A(n,φ))` is solvable.

The field-theoretic core is isolated as `typeACore` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

variable {K : Type*} [Field K] [CharP K 2]

/-! ## The two-step group `A(n,φ)` -/

/-- The Higman group `A(n,φ)`: the two-step group on `K × K` with
`(x,z) * (y,w) = (x + y, z + w + x·φ(y))`. -/
abbrev AG (φ : K ≃+* K) : Type _ := Work.Higman.AType K φ

/-- An element of `A(n,φ)` has order dividing two exactly when its `A`-coordinate vanishes. -/
theorem AG_sq_eq_one_iff (φ : K ≃+* K) (a : AG φ) : a ^ 2 = 1 ↔ a.fst = 0 := by
  rw [TwoStep.sq_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact (RingEquiv.map_eq_zero_iff φ).mp h1
  · intro h
    show a.fst * φ a.fst = 0
    rw [h, zero_mul]

/-- Every element of `A(n,φ)` is the pair of its coordinates. -/
theorem AG_eta (φ : K ≃+* K) (u : AG φ) : u = ⟨u.fst, u.snd⟩ := TwoStep.ext_iff rfl rfl

/-! ## The induced maps on `A/Z = K` and on `Z` -/

section Induced

variable {φ : K ≃+* K}

/-- The first coordinate of `α ⟨x,0⟩`: the map induced by `α` on `A/Z ≅ K`. -/
abbrev indFst (α : MulAut (AG φ)) (x : K) : K := (α ⟨x, 0⟩).1

/-- The second coordinate of `α ⟨x,0⟩`. -/
abbrev indMid (α : MulAut (AG φ)) (x : K) : K := (α ⟨x, 0⟩).2

/-- The map induced by `α` on the subgroup `Z = {(0,z)}` of involutions. -/
abbrev indSnd (α : MulAut (AG φ)) (z : K) : K := (α ⟨0, z⟩).2

theorem indSnd_fst (α : MulAut (AG φ)) (z : K) : (α ⟨0, z⟩).1 = 0 := by
  have h2 : (α ⟨0, z⟩) ^ 2 = 1 := by
    rw [← map_pow]
    show α ((⟨0, z⟩ : AG φ) ^ 2) = 1
    rw [(AG_sq_eq_one_iff φ ⟨0, z⟩).mpr rfl, map_one]
  exact (AG_sq_eq_one_iff φ (α ⟨0, z⟩)).mp h2

theorem indSnd_zero (α : MulAut (AG φ)) : indSnd α 0 = 0 := by
  show (α (1 : AG φ)).2 = 0
  rw [map_one]
  rfl

theorem indMid_zero (α : MulAut (AG φ)) : indMid α 0 = 0 := by
  show (α (⟨0, (0 : K)⟩ : AG φ)).2 = 0
  rw [show (⟨0, (0 : K)⟩ : AG φ) = 1 from rfl, map_one]
  rfl

/-- The action of `α` on a general element, in coordinates. -/
theorem apply_eq (α : MulAut (AG φ)) (x z : K) :
    α ⟨x, z⟩ = ⟨indFst α x, indMid α x + indSnd α z⟩ := by
  have h1 : (⟨x, z⟩ : AG φ) = ⟨x, 0⟩ * ⟨0, z⟩ := by ext <;> simp [aCocycle]
  have hmk : α ⟨x, 0⟩ = ⟨indFst α x, indMid α x⟩ := TwoStep.ext_iff rfl rfl
  have h0 : α ⟨0, z⟩ = ⟨0, indSnd α z⟩ := TwoStep.ext_iff (indSnd_fst α z) rfl
  calc α ⟨x, z⟩ = α (⟨x, 0⟩ * ⟨0, z⟩) := by rw [h1]
    _ = α ⟨x, 0⟩ * α ⟨0, z⟩ := map_mul _ _ _
    _ = ⟨indFst α x, indMid α x⟩ * ⟨0, indSnd α z⟩ := by rw [hmk, h0]
    _ = ⟨indFst α x, indMid α x + indSnd α z⟩ := by ext <;> simp [aCocycle]

theorem indSnd_add (α : MulAut (AG φ)) (z z' : K) :
    indSnd α (z + z') = indSnd α z + indSnd α z' := by
  have h : (⟨0, z + z'⟩ : AG φ) = ⟨0, z⟩ * ⟨0, z'⟩ := by ext <;> simp [aCocycle]
  have key : α ⟨0, z + z'⟩ = α ⟨0, z⟩ * α ⟨0, z'⟩ := by rw [h, map_mul]
  have hR : (α ⟨0, z⟩ * α ⟨0, z'⟩).2 = indSnd α z + indSnd α z' := by
    rw [TwoStep.snd_mul, indSnd_fst α z, indSnd_fst α z']
    simp [aCocycle]
  have h1 := congrArg (fun u : AG φ => u.2) key
  rw [hR] at h1
  exact h1

theorem indFst_add (α : MulAut (AG φ)) (x y : K) :
    indFst α (x + y) = indFst α x + indFst α y := by
  have h : (⟨x + y, 0⟩ : AG φ) = ⟨x, 0⟩ * ⟨y, 0⟩ * ⟨0, x * φ y⟩ := by
    ext <;> simp [aCocycle, CharTwo.add_self_eq_zero]
  have key : α ⟨x + y, 0⟩ = α ⟨x, 0⟩ * α ⟨y, 0⟩ * α ⟨0, x * φ y⟩ := by
    rw [h, map_mul, map_mul]
  have hR : (α ⟨x, 0⟩ * α ⟨y, 0⟩ * α ⟨0, x * φ y⟩).1 = indFst α x + indFst α y := by
    rw [TwoStep.fst_mul, TwoStep.fst_mul, indSnd_fst α (x * φ y), add_zero]
  have h1 := congrArg (fun u : AG φ => u.1) key
  rw [hR] at h1
  exact h1

/-- The second-coordinate relation underlying `g(x φ x) = f x · φ(f x)`. -/
theorem indMid_rel (α : MulAut (AG φ)) (x y : K) :
    indMid α (x + y) + indSnd α (x * φ y)
      = indMid α x + indMid α y + indFst α x * φ (indFst α y) := by
  have h : (⟨x + y, x * φ y⟩ : AG φ) = ⟨x, 0⟩ * ⟨y, 0⟩ := by ext <;> simp [aCocycle]
  have key : α ⟨x + y, x * φ y⟩ = α ⟨x, 0⟩ * α ⟨y, 0⟩ := by rw [h, map_mul]
  have hL : α ⟨x + y, x * φ y⟩ = ⟨indFst α (x + y), indMid α (x + y) + indSnd α (x * φ y)⟩ :=
    apply_eq α (x + y) (x * φ y)
  have hR : α ⟨x, 0⟩ * α ⟨y, 0⟩
      = ⟨indFst α x + indFst α y, indMid α x + indMid α y + indFst α x * φ (indFst α y)⟩ := by
    rw [apply_eq α x 0, apply_eq α y 0, indSnd_zero]
    ext <;> simp [aCocycle]
  rw [hL, hR] at key
  exact congrArg (fun u : AG φ => u.2) key

/-- **The key identity**: `g(x·φ(x)) = f(x)·φ(f(x))`. -/
theorem indSnd_quad (α : MulAut (AG φ)) (x : K) :
    indSnd α (x * φ x) = indFst α x * φ (indFst α x) := by
  have h := indMid_rel α x x
  simp only [CharTwo.add_self_eq_zero, indMid_zero, zero_add] at h
  exact h

theorem indFst_comp (α β : MulAut (AG φ)) (x : K) :
    indFst (α * β) x = indFst α (indFst β x) := by
  have hb : β ⟨x, 0⟩ = ⟨indFst β x, indMid β x⟩ := AG_eta φ _
  have hsplit : (⟨indFst β x, indMid β x⟩ : AG φ) = ⟨indFst β x, 0⟩ * ⟨0, indMid β x⟩ := by
    ext <;> simp [aCocycle]
  calc indFst (α * β) x = ((α * β) ⟨x, 0⟩).1 := rfl
    _ = (α (β ⟨x, 0⟩)).1 := rfl
    _ = (α ⟨indFst β x, indMid β x⟩).1 := by rw [hb]
    _ = (α (⟨indFst β x, 0⟩ * ⟨0, indMid β x⟩)).1 := by rw [hsplit]
    _ = (α ⟨indFst β x, 0⟩ * α ⟨0, indMid β x⟩).1 := by rw [map_mul]
    _ = (α ⟨indFst β x, 0⟩).1 + (α ⟨0, indMid β x⟩).1 := TwoStep.fst_mul _ _
    _ = indFst α (indFst β x) := by rw [indSnd_fst α (indMid β x), add_zero]

theorem indFst_surj (α : MulAut (AG φ)) : Function.Surjective (indFst α) := by
  intro u
  refine ⟨indFst α⁻¹ u, ?_⟩
  rw [← indFst_comp α α⁻¹ u, mul_inv_cancel]
  rfl

theorem indFst_inj (α : MulAut (AG φ)) : Function.Injective (indFst α) := by
  intro a b hab
  have h1 : indFst (α⁻¹ * α) a = indFst (α⁻¹ * α) b := by
    rw [indFst_comp α⁻¹ α a, indFst_comp α⁻¹ α b, hab]
  rw [inv_mul_cancel] at h1
  exact h1

theorem indFst_bij (α : MulAut (AG φ)) : Function.Bijective (indFst α) :=
  ⟨indFst_inj α, indFst_surj α⟩

theorem indFst_ne_zero (α : MulAut (AG φ)) : ∃ x : K, indFst α x ≠ 0 := by
  obtain ⟨x, hx⟩ := indFst_surj α 1
  exact ⟨x, by rw [hx]; exact one_ne_zero⟩

/-- The permutation of `K` induced by `α` (`= f_α`). -/
abbrev indPermFun (α : MulAut (AG φ)) : Equiv.Perm K :=
  Equiv.ofBijective (indFst α) (indFst_bij α)

theorem indPermFun_apply (α : MulAut (AG φ)) (x : K) : indPermFun α x = indFst α x := rfl

/-- `α ↦ f_α` as a homomorphism `Aut(A(n,φ)) →* Perm K`. -/
def indPermHom : MulAut (AG φ) →* Equiv.Perm K where
  toFun := indPermFun
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro a b
    ext x
    show indFst (a * b) x = indFst a (indFst b x)
    exact indFst_comp a b x

end Induced

/-! ## The field-theoretic core (App. VIII, Prop. 1, p. 224)

The core computation `typeACore` — the coefficient comparison for the identity
`g (x·φ(x)) = f(x)·φ(f(x))` with `φ(x) = x^(2^s)` — lives in `AppVIII/typeACore.lean`. -/

/-! ## Consequences of the core for a fixed automorphism -/

/-- The core applied to the induced pair `(f_α, g_α)`. -/
lemma coreApplied {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {n s : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (hsn : s < n) (hs0 : s ≠ 0)
    (h4 : ¬ n ∣ 4 * s) {φ : K ≃+* K} (hφs : ∀ x : K, φ x = x ^ (2 ^ s))
    (α : MulAut (AG φ)) :
    ∃ (lam : K) (i : ℕ), lam ≠ 0 ∧ i < n ∧ (∀ x, indFst α x = lam * x ^ (2 ^ i)) ∧
      (∀ z, indSnd α z = lam * lam ^ (2 ^ s) * z ^ (2 ^ i)) := by
  refine typeACore hcard hsn hs0 h4 (indFst α) (indSnd α) (indFst_add α) (indSnd_add α)
    (indFst_ne_zero α) (fun x => ?_)
  rw [← hφs x, indSnd_quad α x, hφs (indFst α x)]

/-- If `f_α = id` then also `g_α = id`. -/
lemma indSnd_eq_id_of_indFst_eq_id {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    {n s : ℕ} (hcard : Fintype.card K = 2 ^ n) (hsn : s < n) (hs0 : s ≠ 0)
    (h4 : ¬ n ∣ 4 * s) {φ : K ≃+* K} (hφs : ∀ x : K, φ x = x ^ (2 ^ s))
    (α : MulAut (AG φ)) (hα : ∀ x, indFst α x = x) : indSnd α = id := by
  obtain ⟨lam, i, hlam, hi, hf, hg⟩ := coreApplied hcard hsn hs0 h4 hφs α
  have hlam1 : lam = 1 := by
    have h1 := hf 1
    rw [hα 1, one_pow, mul_one] at h1
    exact h1.symm
  have hx : ∀ x : K, x ^ (2 ^ i) = x := by
    intro x
    have h1 := hf x
    rw [hlam1, one_mul, hα x] at h1
    exact h1.symm
  funext z
  calc indSnd α z = lam * lam ^ (2 ^ s) * z ^ (2 ^ i) := hg z
    _ = 1 * 1 ^ (2 ^ s) * z := by rw [hlam1, hx z]
    _ = z := by simp

/-! ## Solvability of `Aut(A(n,φ))` -/

/-- Powers of the Frobenius act as `x ↦ x ^ (2 ^ k)`. -/
lemma frobK_pow_apply_two_pow {K : Type*} [Field K] [CharP K 2] [Finite K] :
    ∀ (k : ℕ) (x : K), (frobK K ^ k) x = x ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => intro x; simp [frobK, frobeniusEquiv_def]
  | succ k ih =>
    intro x
    rw [pow_succ]
    have h1 : ((frobK K ^ k) * frobK K) x = (frobK K ^ k) ((frobK K) x) := rfl
    rw [h1, ih ((frobK K) x)]
    have h2 : (frobK K) x = x ^ 2 := by rw [frobK, frobeniusEquiv_def]
    rw [h2, ← pow_mul]
    congr 1
    rw [pow_succ']

/-- The image of `α ↦ f_α` lies in the semilinear group `Γ`. -/
lemma indPermFun_mem_gammaSet {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    {n s : ℕ} (hcard : Fintype.card K = 2 ^ n) (hsn : s < n)
    (hs0 : s ≠ 0) (h4 : ¬ n ∣ 4 * s) {φ : K ≃+* K} (hφs : ∀ x : K, φ x = x ^ (2 ^ s))
    (α : MulAut (AG φ)) : indPermFun α ∈ gammaSet K := by
  obtain ⟨lam, i, hlam, hi, hf, hg⟩ := coreApplied hcard hsn hs0 h4 hφs α
  refine ⟨lam, ⟨(i : ℤ), hlam, fun x => ?_⟩⟩
  rw [indPermFun_apply, hf x, zpow_natCast, ← frobK_pow_apply_two_pow i x]

/-- The kernel of `α ↦ f_α` is abelian. -/
lemma indPermHom_ker_comm {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    {n s : ℕ} (hcard : Fintype.card K = 2 ^ n) (hsn : s < n)
    (hs0 : s ≠ 0) (h4 : ¬ n ∣ 4 * s) {φ : K ≃+* K} (hφs : ∀ x : K, φ x = x ^ (2 ^ s))
    (a b : (indPermHom (φ := φ)).ker) : a * b = b * a := by
  have ha : ∀ x, indFst (a : MulAut (AG φ)) x = x := by
    intro x
    have h := congrArg (fun f : Equiv.Perm K => f x) (MonoidHom.mem_ker.mp a.2)
    simpa [indPermHom] using h
  have hb : ∀ x, indFst (b : MulAut (AG φ)) x = x := by
    intro x
    have h := congrArg (fun f : Equiv.Perm K => f x) (MonoidHom.mem_ker.mp b.2)
    simpa [indPermHom] using h
  have hsa := indSnd_eq_id_of_indFst_eq_id hcard hsn hs0 h4 hφs (a : MulAut (AG φ)) ha
  have hsb := indSnd_eq_id_of_indFst_eq_id hcard hsn hs0 h4 hφs (b : MulAut (AG φ)) hb
  have hsa' : ∀ w, indSnd (a : MulAut (AG φ)) w = w := fun w => congrFun hsa w
  have hsb' : ∀ w, indSnd (b : MulAut (AG φ)) w = w := fun w => congrFun hsb w
  have ha' : ∀ x z, (a : MulAut (AG φ)) ⟨x, z⟩ = ⟨x, indMid (a : MulAut (AG φ)) x + z⟩ := by
    intro x z
    rw [apply_eq, ha x, hsa' z]
  have hb' : ∀ x z, (b : MulAut (AG φ)) ⟨x, z⟩ = ⟨x, indMid (b : MulAut (AG φ)) x + z⟩ := by
    intro x z
    rw [apply_eq, hb x, hsb' z]
  apply Subtype.ext
  refine MulEquiv.ext (fun u => ?_)
  obtain ⟨x, z⟩ := u
  calc (a : MulAut (AG φ)) ((b : MulAut (AG φ)) ⟨x, z⟩)
      = (a : MulAut (AG φ)) ⟨x, indMid (b : MulAut (AG φ)) x + z⟩ := by rw [hb' x z]
    _ = ⟨x, indMid (a : MulAut (AG φ)) x + (indMid (b : MulAut (AG φ)) x + z)⟩ := by
          rw [ha' x (indMid (b : MulAut (AG φ)) x + z)]
    _ = ⟨x, indMid (b : MulAut (AG φ)) x + (indMid (a : MulAut (AG φ)) x + z)⟩ := by
          congr 1; abel
    _ = (b : MulAut (AG φ)) ⟨x, indMid (a : MulAut (AG φ)) x + z⟩ := by
          rw [hb' x (indMid (a : MulAut (AG φ)) x + z)]
    _ = (b : MulAut (AG φ)) ((a : MulAut (AG φ)) ⟨x, z⟩) := by rw [ha' x z]

/-! ## The theorem -/

theorem appVIIIProp1 : AppVIIIProp1 := by
  intro n φ hφ4
  rcases eq_or_ne n 0 with hn0 | hn
  · subst hn0
    exact absurd (by rw [galoisFieldZero φ, one_pow]) hφ4
  obtain ⟨s, hsn, h4, hφs⟩ := frobPowOfFourth hn φ hφ4
  have hs0 : s ≠ 0 := by rintro rfl; exact h4 (by simp)
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]
  haveI hker : Group.IsSolvable (indPermHom (φ := φ)).ker :=
    Group.isSolvable_of_comm (indPermHom_ker_comm hcard hsn hs0 h4 hφs)
  let gG : MulAut (AG φ) →* gammaLin (GaloisField 2 n) :=
    { toFun := fun a => ⟨indPermHom a, indPermFun_mem_gammaSet hcard hsn hs0 h4 hφs a⟩
      map_one' := Subtype.ext (indPermHom (φ := φ)).map_one
      map_mul' := fun a b => Subtype.ext ((indPermHom (φ := φ)).map_mul a b) }
  have hker_eq : gG.ker = (indPermHom (φ := φ)).ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact Subtype.ext_iff.mp h
    · intro h
      exact Subtype.ext h
  exact Group.isSolvable_of_ker_le_range (indPermHom (φ := φ)).ker.subtype gG
    (le_of_eq (by rw [Subgroup.range_subtype, hker_eq]))

end Work.Hering.AppVIII
