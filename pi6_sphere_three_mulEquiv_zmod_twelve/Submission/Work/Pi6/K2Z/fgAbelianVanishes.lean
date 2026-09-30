import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.zmodTensorSubsingleton
import Submission.Work.Pi6.K2Z.zmodTensorModuleFinite
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# A finitely generated `ℤ`-module is trivial if it vanishes rationally and mod every prime

Let `A` be a finitely generated abelian group.  The base change of `A` along `ℤ → ℚ` (resp.
`ℤ → ZMod p`) is `ℚ ⊗[ℤ] A` (resp. `ZMod p ⊗[ℤ] A = A/pA`).  This file proves that if
`ℚ ⊗[ℤ] A` and `ZMod p ⊗[ℤ] A` for every prime `p` are trivial (equivalently: have `finrank`
zero over the respective field), then `A` itself is trivial.

## Route

The hypothesis on the `ZMod p`-base change is turned into the surjectivity of multiplication
by `p` on `A`: a `ZMod p`-module is trivial iff its `finrank` is zero, and
`ZMod p ⊗[ℤ] A ≅ A / pA`.  Hence `A = pA` for every prime `p`.

Then the structure theorem `AddCommGroup.equiv_free_prod_directSum_zmod` writes

`A ≅ (Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)`,

and the divisibility conditions rule out both nontrivial parts: a nonzero free part would give a
surjection `A ↠ ℤ` and a nontrivial `p`-torsion summand (`e i ≥ 1`) a surjection
`A ↠ ZMod (p i ^ e i)`, on neither of which multiplication by the relevant prime can be
surjective.  (Concretely, `q • x = 1` would exhibit `q` — or rather `p` in `ZMod (p ^ e)` with
`e ≥ 1`, where `p` is nilpotent — as a unit.)

In fact the hypothesis `hr` on the rational base change is not needed: the vanishing of the
`ZMod p`-base change for every prime `p` alone already forces `A = 0`.
-/

open CategoryTheory
open scoped TensorProduct

namespace Work.Pi6.K2Z

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- Surjectivity of multiplication by `q` descends to quotients (additively written). -/
private lemma surj_nsmul_of_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (q : ℕ) (g : A →+ B) (hg : Function.Surjective g)
    (h : ∀ a : A, ∃ b : A, q • b = a) : ∀ y : B, ∃ x : B, q • x = y := by
  intro y
  obtain ⟨a, rfl⟩ := hg y
  obtain ⟨b, hb⟩ := h a
  exact ⟨g b, by rw [← AddMonoidHom.map_nsmul g q b, hb]⟩

theorem fgAbelianVanishes (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (hr : Module.finrank ℚ ↥((ModuleCat.extendScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℤ A)) = 0)
    (hp : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p)
      ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) = 0) :
    Subsingleton A := by
  classical
  -- Step 1: the `ZMod q`-base change is trivial, hence multiplication by `q` is surjective on `A`.
  have hsurj : ∀ q : ℕ, q.Prime → ∀ a : A, ∃ b : A, q • b = a := by
    intro q hq a
    haveI : Fact q.Prime := ⟨hq⟩
    let V := ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod q))).obj (ModuleCat.of ℤ A))
    haveI : Module.Finite (ZMod q) V := zmodTensorModuleFinite A q
    have hfr : Module.finrank (ZMod q) V = 0 := hp q hq
    have hsub : Subsingleton V := by
      have h0 : ∀ x : V, x = 0 :=
        (finrank_zero_iff_forall_zero (K := ZMod q) (V := V)).mp hfr
      exact ⟨fun x y => by rw [h0 x, h0 y]⟩
    obtain ⟨b, hb⟩ := zmodTensorSubsingleton A q hsub a
    refine ⟨b, ?_⟩
    rw [Nat.cast_smul_eq_nsmul ℤ q b] at hb
    exact hb
  -- Step 2: the structure theorem for finitely generated abelian groups.
  haveI : AddGroup.FG A := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨n, ι, _, p, hpp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  -- The free part has rank zero.
  have hn : n = 0 := by
    by_contra hn
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    let j : Fin n := ⟨0, hn'⟩
    -- the projection `A ↠ ℤ`
    let g : A →+ ℤ :=
      { toFun := fun a => (f a).1 j
        map_zero' := by simp
        map_add' := by intro x y; simp [Prod.fst_add] }
    have hg : Function.Surjective g := by
      intro m
      refine ⟨f.symm (Finsupp.single j m, 0), ?_⟩
      show (f (f.symm (Finsupp.single j m, 0))).1 j = m
      rw [f.apply_symm_apply]
      exact Finsupp.single_eq_same
    obtain ⟨x, hx⟩ := surj_nsmul_of_surj 2 g hg (hsurj 2 Nat.prime_two) 1
    simp only [two_nsmul] at hx
    omega
  -- Every torsion summand is trivial.
  have he : ∀ i, e i = 0 := by
    intro i
    by_contra hei
    have hei' : 0 < e i := Nat.pos_of_ne_zero hei
    -- the projection `A ↠ ZMod (p i ^ e i)`
    let g : A →+ ZMod (p i ^ e i) :=
      { toFun := fun a => (f a).2 i
        map_zero' := by simp
        map_add' := by intro x y; simp }
    have hg : Function.Surjective g := by
      intro m
      refine ⟨f.symm (0, DFinsupp.single i m), ?_⟩
      show (f (f.symm (0, DFinsupp.single i m))).2 i = m
      rw [f.apply_symm_apply]
      exact DFinsupp.single_eq_same
    obtain ⟨y, hy⟩ := surj_nsmul_of_surj (p i) g hg (hsurj (p i) (hpp i)) 1
    rw [nsmul_eq_mul] at hy
    have hunit : IsUnit (((p i : ℕ) : ZMod (p i ^ e i))) :=
      ⟨Units.mkOfMulEqOne _ y hy, rfl⟩
    have hpow : (((p i : ℕ) : ZMod (p i ^ e i))) ^ e i = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hzero : IsUnit (0 : ZMod (p i ^ e i)) := by
      rw [← hpow]; exact hunit.pow _
    have h01 : (0 : ZMod (p i ^ e i)) = 1 := isUnit_zero_iff.mp hzero
    have hsub : Subsingleton (ZMod (p i ^ e i)) := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, ← h01, mul_zero]
      have hy' : y = 0 := by rw [← mul_one y, ← h01, mul_zero]
      rw [hx, hy']⟩
    have := ZMod.subsingleton_iff.mp hsub
    have h2 : 1 < p i ^ e i := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hei') (hpp i).one_lt
    omega
  -- Step 3: both factors of the decomposition are trivial, hence so is `A`.
  have h1 : Subsingleton (Fin n →₀ ℤ) := by
    rw [hn]
    exact ⟨fun x y => by ext a; exact Fin.elim0 a⟩
  have h2 : Subsingleton (DirectSum ι fun i => ZMod (p i ^ e i)) := by
    constructor
    intro x y
    ext i
    have : Subsingleton (ZMod (p i ^ e i)) := by rw [he i, pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  exact ⟨fun x y => f.injective (by
    apply Prod.ext
    · exact h1.elim _ _
    · exact h2.elim _ _)⟩

end Work.Pi6.K2Z
