import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.End

set_option autoImplicit false

/-!
# Signed-permutation normal form for automorphisms of the free group

An automorphism `α` of `F_n` is a *signed permutation* if it sends each basis
generator to a single basis generator or its inverse.  Equivalently there is a
permutation `σ : Equiv.Perm (Fin n)` and a sign function `s : Fin n → Bool`
(`true` = +1, `false` = −1) such that

    α (a_i) = a_{σ i}  if `s i = true`,    α (a_i) = (a_{σ i})⁻¹  otherwise.

Every such `α` is an automorphism (the inverse uses the same permutation and
the same signs: `α⁻¹ (a_j) = a_{σ⁻¹ j}^{s (σ⁻¹ j)}`, since `±1` is its own
group-theoretic inverse as an exponent), the representation `(σ, s)` is
unique, and composition is `(σ,s) ∘ (τ,t) = (σ∘τ, s∘τ ⊕ t)` (signs XOR).  The
normal form is the terminal case of Nielsen's induction: a basis tuple which
admits no shortening move must be a signed permutation.
-/

namespace Submission.Nielsen

noncomputable section

open FreeGroup

variable {n : ℕ}

/-- The forward homomorphism of the signed permutation `(σ, s)`. -/
def signedAutHom (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun i : Fin n => if s i then FreeGroup.of (σ i) else (FreeGroup.of (σ i))⁻¹)

/-- The inverse homomorphism of the signed permutation `(σ, s)`. -/
def signedAutInvHom (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun j : Fin n => if s (σ.symm j) then FreeGroup.of (σ.symm j) else (FreeGroup.of (σ.symm j))⁻¹)

lemma signedAutInvHom_comp_signedAutHom (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    (signedAutInvHom σ s).comp (signedAutHom σ s) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  have hh : (signedAutHom σ s) (FreeGroup.of k) =
      (if s k = true then FreeGroup.of (σ k) else (FreeGroup.of (σ k))⁻¹) := by
    simp [signedAutHom]
  by_cases hk : s k = true
  · calc
      (signedAutInvHom σ s) ((signedAutHom σ s) (FreeGroup.of k))
          = (signedAutInvHom σ s) (FreeGroup.of (σ k)) := by rw [hh, if_pos hk]
      _ = FreeGroup.of k := by
            have heq : σ.symm (σ k) = k := Equiv.symm_apply_apply σ k
            have hcond : s (σ.symm (σ k)) = true := by rw [heq]; exact hk
            rw [signedAutInvHom]
            rw [FreeGroup.lift_apply_of]
            rw [if_pos hcond, heq]
  · calc
      (signedAutInvHom σ s) ((signedAutHom σ s) (FreeGroup.of k))
          = (signedAutInvHom σ s) ((FreeGroup.of (σ k))⁻¹) := by rw [hh, if_neg hk]
      _ = ((signedAutInvHom σ s) (FreeGroup.of (σ k)))⁻¹ := by
            rw [(signedAutInvHom σ s).map_inv]
      _ = ((FreeGroup.of k)⁻¹)⁻¹ := by
            have hsf : s k = false := by
              cases hsk : s k with
              | true => exact False.elim (hk hsk)
              | false => rfl
            have heq : σ.symm (σ k) = k := Equiv.symm_apply_apply σ k
            have hcond : s (σ.symm (σ k)) = false := by rw [heq]; exact hsf
            have hne : ¬ s (σ.symm (σ k)) = true := by rw [hcond]; simp
            have hval : (signedAutInvHom σ s) (FreeGroup.of (σ k)) = (FreeGroup.of k)⁻¹ := by
              rw [signedAutInvHom]
              rw [FreeGroup.lift_apply_of]
              rw [if_neg hne, heq]
            rw [hval]
      _ = FreeGroup.of k := by
            simp

lemma signedAutHom_comp_signedAutInvHom (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    (signedAutHom σ s).comp (signedAutInvHom σ s) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  have hh : (signedAutInvHom σ s) (FreeGroup.of k) =
      (if s (σ.symm k) = true then FreeGroup.of (σ.symm k) else (FreeGroup.of (σ.symm k))⁻¹) := by
    simp [signedAutInvHom]
  by_cases hk : s (σ.symm k) = true
  · calc
      (signedAutHom σ s) ((signedAutInvHom σ s) (FreeGroup.of k))
          = (signedAutHom σ s) (FreeGroup.of (σ.symm k)) := by rw [hh, if_pos hk]
      _ = FreeGroup.of k := by
            have heq : σ (σ.symm k) = k := Equiv.apply_symm_apply σ k
            have hcond : s (σ.symm k) = true := hk
            rw [signedAutHom]
            rw [FreeGroup.lift_apply_of]
            rw [if_pos hcond, heq]
  · calc
      (signedAutHom σ s) ((signedAutInvHom σ s) (FreeGroup.of k))
          = (signedAutHom σ s) ((FreeGroup.of (σ.symm k))⁻¹) := by rw [hh, if_neg hk]
      _ = ((signedAutHom σ s) (FreeGroup.of (σ.symm k)))⁻¹ := by
            rw [(signedAutHom σ s).map_inv]
      _ = ((FreeGroup.of k)⁻¹)⁻¹ := by
            have hsf : s (σ.symm k) = false := by
              cases hsk : s (σ.symm k) with
              | true => exact False.elim (hk hsk)
              | false => rfl
            have heq : σ (σ.symm k) = k := Equiv.apply_symm_apply σ k
            have hcond : s (σ.symm k) = false := hsf
            have hne : ¬ s (σ.symm k) = true := by rw [hcond]; simp
            have hval : (signedAutHom σ s) (FreeGroup.of (σ.symm k)) = (FreeGroup.of k)⁻¹ := by
              rw [signedAutHom]
              rw [FreeGroup.lift_apply_of]
              rw [if_neg hne, heq]
            rw [hval]
      _ = FreeGroup.of k := by
            simp

/-- The automorphism of `F_n` which sends `a_i` to `a_{σ i}` (if `s i`) or to
its inverse (otherwise). -/
def signedAut (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) : MulAut (FreeGroup (Fin n)) where
  toFun := signedAutHom σ s
  invFun := signedAutInvHom σ s
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (signedAutInvHom_comp_signedAutHom σ s)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (signedAutHom_comp_signedAutInvHom σ s)
    simpa using h
  map_mul' x y := (signedAutHom σ s).map_mul x y

/-- `signedAut σ s` acts on the basis generators by single letters. -/
lemma signedAut_apply {σ : Equiv.Perm (Fin n)} {s : Fin n → Bool} (i : Fin n) :
    (signedAut σ s) (FreeGroup.of i) =
      if s i then FreeGroup.of (σ i) else (FreeGroup.of (σ i))⁻¹ := by
  simp [signedAut, signedAutHom]

/-- An automorphism is a signed permutation if every basis generator is mapped
to a single basis generator or its inverse. -/
def IsSignedPermutation (α : MulAut (FreeGroup (Fin n))) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool), α = signedAut σ s

/-- Every `signedAut` is a signed permutation. -/
lemma signedAut_isSignedPermutation (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool) :
    IsSignedPermutation (signedAut σ s) :=
  ⟨σ, s, rfl⟩

/-- Product of two signs (as `±1`, with `true` = `+1`): the product is `+1`
exactly when the two signs agree. -/
def signMul (x y : Bool) : Bool := x == y

/-- Composition law: `(σ,s) ∘ (τ,t) = (σ∘τ, (s∘τ) ⊕ t)` (signs as
`±1`, so "XOR" is `==`). -/
lemma signedAut_mul (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool) :
    signedAut σ s * signedAut τ t =
      signedAut (τ.trans σ) (fun i => signMul (s (τ i)) (t i)) := by
  ext x
  change (signedAutHom σ s) ((signedAutHom τ t) x) =
    (signedAutHom (τ.trans σ) (fun i => signMul (s (τ i)) (t i))) x
  have hh : (signedAutHom σ s).comp (signedAutHom τ t) =
      signedAutHom (τ.trans σ) (fun i => signMul (s (τ i)) (t i)) := by
    apply FreeGroup.ext_hom
    intro i
    have htarget : (signedAutHom (τ.trans σ) (fun j : Fin n => signMul (s (τ j)) (t j)))
          (FreeGroup.of i) =
        (if signMul (s (τ i)) (t i) = true then FreeGroup.of ((τ.trans σ) i)
          else (FreeGroup.of ((τ.trans σ) i))⁻¹) := by
      simp [signedAutHom]
    rw [htarget]
    -- reduce the left side by cases on the two signs
    by_cases hti : t i = true
    · by_cases hsi : s (τ i) = true
      · -- t i = true, s (τ i) = true: both plus signs
        calc
          (signedAutHom σ s) ((signedAutHom τ t) (FreeGroup.of i))
              = (signedAutHom σ s) (FreeGroup.of (τ i)) := by simp [signedAutHom, hti]
          _ = FreeGroup.of (σ (τ i)) := by simp [signedAutHom, hsi]
          _ = (if signMul (s (τ i)) (t i) = true then FreeGroup.of ((τ.trans σ) i)
                else (FreeGroup.of ((τ.trans σ) i))⁻¹) := by
                simp [signMul, hti, hsi]
      · -- t i = true, s (τ i) = false
        have hsf : s (τ i) = false := by
          cases hsk : s (τ i) with
          | true => exact False.elim (hsi hsk)
          | false => rfl
        calc
          (signedAutHom σ s) ((signedAutHom τ t) (FreeGroup.of i))
              = (signedAutHom σ s) (FreeGroup.of (τ i)) := by simp [signedAutHom, hti]
          _ = (FreeGroup.of (σ (τ i)))⁻¹ := by simp [signedAutHom, hsf]
          _ = (if signMul (s (τ i)) (t i) = true then FreeGroup.of ((τ.trans σ) i)
                else (FreeGroup.of ((τ.trans σ) i))⁻¹) := by
                simp [signMul, hti, hsf]
    · by_cases hsi : s (τ i) = true
      · -- t i = false, s (τ i) = true
        have htf : t i = false := by
          cases htk : t i with
          | true => exact False.elim (hti htk)
          | false => rfl
        calc
          (signedAutHom σ s) ((signedAutHom τ t) (FreeGroup.of i))
              = (signedAutHom σ s) ((FreeGroup.of (τ i))⁻¹) := by simp [signedAutHom, htf]
          _ = ((signedAutHom σ s) (FreeGroup.of (τ i)))⁻¹ := by
                rw [(signedAutHom σ s).map_inv]
          _ = (FreeGroup.of (σ (τ i)))⁻¹ := by
                have hval : (signedAutHom σ s) (FreeGroup.of (τ i)) = FreeGroup.of (σ (τ i)) := by
                  simp [signedAutHom, hsi]
                rw [hval]
          _ = (if signMul (s (τ i)) (t i) = true then FreeGroup.of ((τ.trans σ) i)
                else (FreeGroup.of ((τ.trans σ) i))⁻¹) := by
                simp [signMul, htf, hsi]
      · -- t i = false, s (τ i) = false
        have htf : t i = false := by
          cases htk : t i with
          | true => exact False.elim (hti htk)
          | false => rfl
        have hsf : s (τ i) = false := by
          cases hsk : s (τ i) with
          | true => exact False.elim (hsi hsk)
          | false => rfl
        calc
          (signedAutHom σ s) ((signedAutHom τ t) (FreeGroup.of i))
              = (signedAutHom σ s) ((FreeGroup.of (τ i))⁻¹) := by simp [signedAutHom, htf]
          _ = ((signedAutHom σ s) (FreeGroup.of (τ i)))⁻¹ := by
                rw [(signedAutHom σ s).map_inv]
          _ = FreeGroup.of (σ (τ i)) := by
                have hval : (signedAutHom σ s) (FreeGroup.of (τ i)) = (FreeGroup.of (σ (τ i)))⁻¹ := by
                  simp [signedAutHom, hsf]
                rw [hval]
                simp
          _ = (if signMul (s (τ i)) (t i) = true then FreeGroup.of ((τ.trans σ) i)
                else (FreeGroup.of ((τ.trans σ) i))⁻¹) := by
                simp [signMul, htf, hsf]
  simpa using congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x) hh

/-- The reduced word of `signedAut σ s (a_i)` is the single letter `(σ i, s i)`. -/
lemma signedAut_toWord {σ : Equiv.Perm (Fin n)} {s : Fin n → Bool} (i : Fin n) :
    FreeGroup.toWord ((signedAut σ s) (FreeGroup.of i)) = [(σ i, s i)] := by
  rw [signedAut_apply]
  cases s i <;> simp [FreeGroup.toWord_inv, FreeGroup.invRev]

/-- Uniqueness of the signed-permutation data. -/
lemma signedAut_ext (σ τ : Equiv.Perm (Fin n)) (s t : Fin n → Bool)
    (h : signedAut σ s = signedAut τ t) : σ = τ ∧ s = t := by
  classical
  have hp : ∀ i : Fin n, (σ i, s i) = (τ i, t i) := by
    intro i
    have hlt : FreeGroup.toWord ((signedAut σ s) (FreeGroup.of i)) =
        FreeGroup.toWord ((signedAut τ t) (FreeGroup.of i)) := by
      exact congrArg (fun φ : MulAut (FreeGroup (Fin n)) =>
        FreeGroup.toWord (φ (FreeGroup.of i))) h
    rw [signedAut_toWord, signedAut_toWord] at hlt
    have hp0 : some (σ i, s i) = some (τ i, t i) := by
      simpa using congrArg (fun L : List (Fin n × Bool) => L.head?) hlt
    exact Option.some.inj hp0
  constructor
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (hp i)
  · funext i
    exact congrArg Prod.snd (hp i)

/-- The normal-form theorem (existence and uniqueness). -/
theorem signed_perm_normal_form (α : MulAut (FreeGroup (Fin n))) :
    IsSignedPermutation α ↔
      ∃! p : Equiv.Perm (Fin n) × (Fin n → Bool), α = signedAut p.1 p.2 := by
  classical
  constructor
  · intro hα
    rcases hα with ⟨σ, s, rfl⟩
    refine ⟨(σ, s), rfl, ?_⟩
    intro p hp
    have heq : signedAut p.1 p.2 = signedAut σ s := by
      rw [← hp]
    rcases signedAut_ext p.1 σ p.2 s heq with ⟨hσ, hs⟩
    exact Prod.ext hσ hs
  · intro h
    rcases h with ⟨p, hp, _⟩
    exact ⟨p.1, p.2, hp⟩

end

end Submission.Nielsen
