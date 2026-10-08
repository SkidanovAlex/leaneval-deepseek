import Mathlib
import Submission.Work.Higman.aeval_annihilates_module

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open Polynomial

/-! ## Arithmetic in a module over `ZMod 2` -/

section ZModTwoArith

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma add_self_zmod2 (x : V) : x + x = 0 := by
  have h : (2 : ZMod 2) • x = x + x := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private lemma eq_of_add_eq_zero_zmod2 {x y : V} (h : x + y = 0) : x = y := by
  calc x = x + 0 := (add_zero x).symm
    _ = x + (y + y) := by rw [add_self_zmod2 y]
    _ = (x + y) + y := by rw [add_assoc]
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

private lemma eq_add_of_add_add_eq_zero_zmod2 {a b c : V} (h : a + b + c = 0) : a = b + c := by
  have h' : a + (b + c) = 0 := by rw [← add_assoc]; exact h
  exact eq_of_add_eq_zero_zmod2 h'

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

end ZModTwoArith

/-! ## The additive (`ZMod 2`-module) form of the lemma

Let `V` be a finite `ZMod 2`-module and `ξ` a linear automorphism of `V` permuting the nonzero
vectors transitively.  Then every `ξ`-equivariant alternating biadditive `c : V → V → V` vanishes.

Proof sketch: choose `u ≠ 0`.  Since every nonzero vector is `ξ ^ k u`, the vector `u` generates
`V` as a `Polynomial (ZMod 2)`-module, so a polynomial in `ξ` annihilating `u` annihilates all of
`V`.  Writing `M z` for the (well defined) polynomial in `ξ` with `M z u = z`, one shows
`c z y = c u (M z y)` for all `z`, `y`; also `c u (M z z) = c z z = 0` exhibits a nonzero subspace
on which `c u` vanishes, while `c z y = c u (M z y)` shows that the image of `c` is contained in
the image of `c u`. -/

private theorem equivariant_bihom_trivial_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V]
    (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    (c : V → V → V)
    (hmul : ∀ a b d : V, c (a + b) d = c a d + c b d)
    (hmul' : ∀ a b d : V, c a (b + d) = c a b + c a d)
    (halt : ∀ a : V, c a a = 0)
    (heq : ∀ a b : V, ξ (c a b) = c (ξ a) (ξ b)) :
    ∀ a b : V, c a b = 0 := by
  have czl : ∀ y : V, c 0 y = 0 := by
    intro y
    have h := hmul 0 0 y
    rw [zero_add] at h
    exact h.trans (add_self_zmod2 (c 0 y))
  have czr : ∀ x : V, c x 0 = 0 := by
    intro x
    have h := hmul' x 0 0
    rw [add_zero] at h
    exact h.trans (add_self_zmod2 (c x 0))
  by_cases htriv : ∀ x : V, x = 0
  · intro a b
    rw [htriv a]
    exact czl b
  · push_neg at htriv
    obtain ⟨u, hu⟩ := htriv
    -- irreducibility: a nonzero `ξ`-invariant subspace is everything
    have irred : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ W, ξ x ∈ W) →
        (∃ x ∈ W, x ≠ 0) → W = ⊤ := by
      intro W hW hne
      obtain ⟨x, hxW, hx0⟩ := hne
      have pow_mem : ∀ k : ℕ, (ξ ^ k) x ∈ W := by
        intro k
        induction k with
        | zero => simpa using hxW
        | succ k ih =>
            rw [pow_succ', LinearEquiv.mul_apply]
            exact hW _ ih
      rw [Submodule.eq_top_iff']
      intro v
      rcases eq_or_ne v 0 with rfl | hv
      · exact W.zero_mem
      · obtain ⟨k, hk⟩ := htrans x v hx0 hv
        have hmem := pow_mem k
        rwa [hk] at hmem
    -- polynomial calculus in `ξ`
    let ξE : Module.End (ZMod 2) V := ξ.toLinearMap
    let θ : Polynomial (ZMod 2) →ₐ[ZMod 2] Module.End (ZMod 2) V := Polynomial.aeval ξE
    have hθX : θ Polynomial.X = ξE := Polynomial.aeval_X ξE
    have hθpow : ∀ k : ℕ, θ (Polynomial.X ^ k) = ξE ^ k := by
      intro k
      rw [map_pow, hθX]
    have hiterE : ∀ (k : ℕ) (x : V), (ξE ^ k) x = (⇑ξ)^[k] x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
          intro x
          rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
          rfl
    have hpowE : ∀ (k : ℕ) (x : V), (ξE ^ k) x = (ξ ^ k) x := by
      intro k x
      rw [hiterE k x, LinearEquiv.pow_apply]
    -- every nonzero vector is `ξ ^ k u`
    have hgen : ∀ z : V, z = 0 ∨ ∃ k : ℕ, (ξ ^ k) u = z := by
      intro z
      rcases eq_or_ne z 0 with h | h
      · exact Or.inl h
      · exact Or.inr (htrans u z hu h)
    -- a polynomial killing `u` kills everything (a nonzero vector generates the module)
    have hθ_inj : ∀ p : Polynomial (ZMod 2), θ p u = 0 → θ p = 0 :=
      fun p hp => aeval_annihilates_module ξ htrans hu p hp
    have exists_poly : ∀ z : V, ∃ p : Polynomial (ZMod 2), θ p u = z := by
      intro z
      rcases eq_or_ne z 0 with rfl | hz
      · exact ⟨0, by simp⟩
      · obtain ⟨k, hk⟩ := htrans u z hu hz
        exact ⟨Polynomial.X ^ k, by rw [hθpow, hpowE k u, hk]⟩
    -- the "multiplication" `M z`, the unique polynomial in `ξ` sending `u` to `z`
    let pz : V → Polynomial (ZMod 2) := fun z => Classical.choose (exists_poly z)
    have pz_spec : ∀ z : V, θ (pz z) u = z := fun z => Classical.choose_spec (exists_poly z)
    let M : V → Module.End (ZMod 2) V := fun z => θ (pz z)
    have M_spec : ∀ z : V, M z u = z := pz_spec
    have M_add : ∀ z₁ z₂ : V, M (z₁ + z₂) = M z₁ + M z₂ := by
      intro z₁ z₂
      have hu0 : θ (pz (z₁ + z₂) + pz z₁ + pz z₂) u = 0 := by
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, pz_spec, pz_spec,
          pz_spec]
        rw [show (z₁ + z₂) + z₁ + z₂ = (z₁ + z₁) + (z₂ + z₂) from by abel, add_self_zmod2,
          add_self_zmod2, add_zero]
      have h0 := hθ_inj _ hu0
      rw [map_add, map_add] at h0
      exact eq_add_of_add_add_eq_zero_zmod2 h0
    have M_comm : ∀ z₁ z₂ : V, M z₁ z₂ = M z₂ z₁ := by
      intro z₁ z₂
      calc M z₁ z₂ = M z₁ (M z₂ u) := by rw [M_spec z₂]
        _ = (M z₁ * M z₂) u := by rw [Module.End.mul_apply]
        _ = (θ (pz z₁) * θ (pz z₂)) u := rfl
        _ = θ (pz z₁ * pz z₂) u := by rw [map_mul]
        _ = θ (pz z₂ * pz z₁) u := by rw [mul_comm (pz z₁) (pz z₂)]
        _ = (θ (pz z₂) * θ (pz z₁)) u := by rw [map_mul]
        _ = (M z₂ * M z₁) u := rfl
        _ = M z₂ (M z₁ u) := by rw [Module.End.mul_apply]
        _ = M z₂ z₁ := by rw [M_spec z₁]
    have M_u : M u = 1 := by
      have hu0 : θ (pz u + 1) u = 0 := by
        rw [map_add, LinearMap.add_apply, pz_spec, map_one, Module.End.one_apply]
        exact add_self_zmod2 u
      have h0 := hθ_inj _ hu0
      rw [map_add, map_one] at h0
      show θ (pz u) = 1
      exact eq_of_add_eq_zero_zmod2 h0
    have M_xi : ∀ k : ℕ, M ((ξ ^ k) u) = ξE ^ k := by
      intro k
      have hu0 : θ (pz ((ξ ^ k) u) + Polynomial.X ^ k) u = 0 := by
        rw [map_add, LinearMap.add_apply, pz_spec, hθpow, hpowE k u]
        exact add_self_zmod2 ((ξ ^ k) u)
      have h0 := hθ_inj _ hu0
      rw [map_add, hθpow] at h0
      show θ (pz ((ξ ^ k) u)) = ξE ^ k
      exact eq_of_add_eq_zero_zmod2 h0
    -- iterated equivariance
    have heqpow : ∀ (k : ℕ) (x y : V), c ((ξ ^ k) x) ((ξ ^ k) y) = (ξ ^ k) (c x y) := by
      intro k
      induction k with
      | zero => intro x y; rfl
      | succ k ih =>
          intro x y
          have hx : (ξ ^ (k + 1)) x = (ξ ^ k) (ξ x) := by
            rw [pow_succ, LinearEquiv.mul_apply]
          have hy : (ξ ^ (k + 1)) y = (ξ ^ k) (ξ y) := by
            rw [pow_succ, LinearEquiv.mul_apply]
          have hstep : (ξ ^ (k + 1)) (c x y) = (ξ ^ k) (ξ (c x y)) := by
            rw [pow_succ, LinearEquiv.mul_apply]
          rw [hx, hy, ih (ξ x) (ξ y), ← heq, hstep]
    -- self-adjointness of the powers of `ξ`
    have hS : ∀ (i : ℕ) (x y : V), c ((ξ ^ i) x) y = c x ((ξ ^ i) y) := by
      intro i x y
      by_cases hfix : (ξ ^ i) u = u
      · have hid : ∀ z : V, (ξ ^ i) z = z := by
          intro z
          rcases eq_or_ne z 0 with rfl | hz
          · rw [map_zero]
          · obtain ⟨k, hk⟩ := htrans u z hu hz
            rw [← hk]
            have h1 : (ξ ^ i) ((ξ ^ k) u) = (ξ ^ k) ((ξ ^ i) u) := by
              rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_add, ← pow_add,
                add_comm]
            rw [h1, hfix]
        rw [hid x, hid y]
      · have hz : (ξ ^ i) u + u ≠ 0 := fun hc => hfix (eq_of_add_eq_zero_zmod2 hc)
        obtain ⟨j, hj⟩ := htrans u ((ξ ^ i) u + u) hu hz
        have hj_eq : ξE ^ j = ξE ^ i + 1 := by
          have hu0 : θ (Polynomial.X ^ j + Polynomial.X ^ i + 1) u = 0 := by
            rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hθpow, hθpow,
              map_one, Module.End.one_apply, hpowE j u, hpowE i u]
            rw [hj]
            rw [show ((ξ ^ i) u + u) + (ξ ^ i) u + u
                = ((ξ ^ i) u + (ξ ^ i) u) + (u + u) from by abel, add_self_zmod2,
              add_self_zmod2, add_zero]
          have h0 := hθ_inj _ hu0
          rw [map_add, map_add, hθpow, hθpow, map_one] at h0
          exact eq_add_of_add_add_eq_zero_zmod2 h0
        have hxj : ∀ x : V, (ξ ^ j) x = (ξ ^ i) x + x := by
          intro x
          have hx := congrArg (fun f : Module.End (ZMod 2) V => f x) hj_eq
          rw [LinearMap.add_apply, Module.End.one_apply] at hx
          rw [← hpowE j x, ← hpowE i x]
          exact hx
        have e1 : c ((ξ ^ j) x) ((ξ ^ j) y) = (ξ ^ i) (c x y) + c x y := by
          rw [heqpow j, ← hpowE j (c x y), hj_eq, LinearMap.add_apply, Module.End.one_apply,
            ← hpowE i (c x y)]
        have e2 : c ((ξ ^ j) x) ((ξ ^ j) y)
            = ((ξ ^ i) (c x y) + c x ((ξ ^ i) y)) + (c ((ξ ^ i) x) y + c x y) := by
          rw [hxj x, hxj y, hmul' ((ξ ^ i) x + x) ((ξ ^ i) y) y,
            hmul ((ξ ^ i) x) x ((ξ ^ i) y), hmul ((ξ ^ i) x) x y, heqpow i]
        have hzero : c x ((ξ ^ i) y) + c ((ξ ^ i) x) y = 0 := by
          have hEq : ((ξ ^ i) (c x y) + c x ((ξ ^ i) y)) + (c ((ξ ^ i) x) y + c x y)
              = (ξ ^ i) (c x y) + c x y := by rw [← e2, e1]
          have h4 : (c x ((ξ ^ i) y) + c ((ξ ^ i) x) y) + ((ξ ^ i) (c x y) + c x y)
              = (ξ ^ i) (c x y) + c x y := by
            conv_rhs => rw [← hEq]
            abel
          have h5 : (c x ((ξ ^ i) y) + c ((ξ ^ i) x) y) + ((ξ ^ i) (c x y) + c x y)
              + ((ξ ^ i) (c x y) + c x y) = 0 := by rw [h4, add_self_zmod2]
          have h6 : (c x ((ξ ^ i) y) + c ((ξ ^ i) x) y) + ((ξ ^ i) (c x y) + c x y)
              + ((ξ ^ i) (c x y) + c x y)
              = c x ((ξ ^ i) y) + c ((ξ ^ i) x) y := by
            rw [show (c x ((ξ ^ i) y) + c ((ξ ^ i) x) y) + ((ξ ^ i) (c x y) + c x y)
                  + ((ξ ^ i) (c x y) + c x y)
                = (c x ((ξ ^ i) y) + c ((ξ ^ i) x) y)
                  + (((ξ ^ i) (c x y) + c x y) + ((ξ ^ i) (c x y) + c x y)) from by abel,
              add_self_zmod2, add_zero]
          rw [h6] at h5
          exact h5
        exact (eq_of_add_eq_zero_zmod2 hzero).symm
    -- homogeneity of `c` in `ZMod 2`-scalars
    have hsmulL : ∀ (a : ZMod 2) (z y : V), c (a • z) y = a • c z y := by
      intro a z y
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · rw [zero_smul, czl, zero_smul]
      · rw [one_smul, one_smul]
    have hsmulR : ∀ (a : ZMod 2) (z y : V), c z (a • y) = a • c z y := by
      intro a z y
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · rw [zero_smul, czr, zero_smul]
      · rw [one_smul, one_smul]
    -- `c z y = c u (M z y)`
    have hMain : ∀ (p : Polynomial (ZMod 2)) (y : V), c (θ p u) y = c u (θ p y) := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          intro y
          have hL : c (θ (p + q) u) y = c (θ p u) y + c (θ q u) y := by
            rw [map_add, LinearMap.add_apply, hmul]
          have hR : c u (θ (p + q) y) = c u (θ p y) + c u (θ q y) := by
            rw [map_add, LinearMap.add_apply, hmul']
          rw [hL, hR, hp y, hq y]
      | monomial n a =>
          intro y
          have hmono : θ (Polynomial.monomial n a) = a • (ξE ^ n) := by
            rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
              Algebra.smul_mul_assoc, one_mul]
          rw [hmono, LinearMap.smul_apply, LinearMap.smul_apply, hpowE n u, hpowE n y,
            hsmulL, hS n u y, hsmulR]
    have hM : ∀ z y : V, c z y = c u (M z y) := by
      intro z y
      have h := hMain (pz z) y
      rw [pz_spec z] at h
      exact h
    -- suppose `c` does not vanish
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₀, y₀, hz₀⟩ := hcon
    let φ : V →ₗ[ZMod 2] V :=
      { toFun := fun y => c u y
        map_add' := fun y₁ y₂ => hmul' u y₁ y₂
        map_smul' := fun a y => hsmulR a u y }
    let W : Submodule (ZMod 2) V :=
      Submodule.span (ZMod 2) (Set.range (fun p : V × V => c p.1 p.2))
    have hWmem : ∀ p : V × V, c p.1 p.2 ∈ W := fun p => Submodule.subset_span ⟨p, rfl⟩
    have hWne : ∃ x ∈ W, x ≠ 0 := ⟨c z₀ y₀, hWmem (z₀, y₀), hz₀⟩
    have hWin : ∀ w ∈ W, ξ w ∈ W := by
      intro w hw
      refine Submodule.span_induction (p := fun x _ => ξ x ∈ W) ?_ ?_ ?_ ?_ hw
      · rintro w ⟨⟨z, y⟩, rfl⟩
        exact Submodule.subset_span ⟨(ξ z, ξ y), (heq z y).symm⟩
      · rw [map_zero]
        exact W.zero_mem
      · intro x y hx hy ihx ihy
        rw [map_add]
        exact W.add_mem ihx ihy
      · intro a x hx ih
        rw [map_smul]
        exact W.smul_mem a ih
    have hWtop : W = ⊤ := irred W hWin hWne
    have hle : W ≤ φ.range := by
      rw [Submodule.span_le]
      rintro w ⟨⟨z, y⟩, rfl⟩
      change c z y ∈ φ.range
      rw [LinearMap.mem_range]
      exact ⟨M z y, (hM z y).symm⟩
    have hφtop : φ.range = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hle (by rw [hWtop]; exact Submodule.mem_top)
    have hsurj : Function.Surjective φ := LinearMap.range_eq_top.mp hφtop
    have hinj : Function.Injective φ := Finite.injective_iff_surjective.mpr hsurj
    have hcontr : φ u = φ 0 := by
      show c u u = c u 0
      rw [halt u, czr u]
    exact hu (hinj hcontr)

/-! ## The statement -/

/-- **Gorenstein–Thompson (Higman 1963, Lemma 4), elementary abelian form.**  Let `A` be a
finite elementary abelian `2`-group with an automorphism `ξ` acting transitively on `A \ {1}`.
Then every alternating `ξ`-equivariant bihomomorphism `c : A × A → A` is trivial. -/
theorem equivariant_bihom_trivial {A : Type*} [CommGroup A] [Finite A]
    (h2 : ∀ a : A, a * a = 1) (ξ : MulAut A)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b)
    (c : A → A → A)
    (hmul : ∀ a b d : A, c (a * b) d = c a d * c b d)
    (hmul' : ∀ a b d : A, c a (b * d) = c a b * c a d)
    (halt : ∀ a : A, c a a = 1)
    (heq : ∀ a b : A, ξ (c a b) = c (ξ a) (ξ b)) :
    ∀ a b : A, c a b = 1 := by
  have h02 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    show Additive.ofMul (x.toMul * x.toMul) = Additive.ofMul (1 : A)
    rw [h2 x.toMul]
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) h02
  -- `ξ` as a `ZMod 2`-linear equivalence
  let ξa : Additive A ≃+ Additive A := ξ.toAdditive
  have hξa_smul : ∀ (m : ZMod 2) (x : Additive A), ξa (m • x) = m • ξa x := by
    intro m x
    rcases zmod2_eq_zero_or_one m with rfl | rfl
    · rw [zero_smul, zero_smul]
      exact map_zero ξa
    · rw [one_smul, one_smul]
  let ξ' : Additive A ≃ₗ[ZMod 2] Additive A := AddEquiv.toLinearEquiv ξa hξa_smul
  have hξpow : ∀ (k : ℕ) (a : A), (⇑ξ)^[k] a = (ξ ^ k) a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
        intro a
        rw [Function.iterate_succ_apply, ih (ξ a), pow_succ]
        rfl
  have hξ'iter : ∀ (k : ℕ) (a : A),
      (⇑ξ')^[k] (Additive.ofMul a) = Additive.ofMul ((⇑ξ)^[k] a) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
        intro a
        have hstep : ξ' (Additive.ofMul a) = Additive.ofMul (ξ a) := rfl
        rw [Function.iterate_succ_apply, hstep, ih (ξ a), Function.iterate_succ_apply]
  have hξ'pow : ∀ (k : ℕ) (a : A),
      (ξ' ^ k) (Additive.ofMul a) = Additive.ofMul ((ξ ^ k) a) := by
    intro k a
    rw [LinearEquiv.pow_apply, hξ'iter k a, ← hξpow k a]
  have htrans' : ∀ a b : Additive A, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ' ^ k) a = b := by
    intro a b ha hb
    have ha' : a.toMul ≠ 1 := by
      intro h
      apply ha
      show Additive.ofMul a.toMul = (0 : Additive A)
      rw [h]
      rfl
    have hb' : b.toMul ≠ 1 := by
      intro h
      apply hb
      show Additive.ofMul b.toMul = (0 : Additive A)
      rw [h]
      rfl
    obtain ⟨k, hk⟩ := htrans a.toMul b.toMul ha' hb'
    refine ⟨k, ?_⟩
    show (ξ' ^ k) (Additive.ofMul a.toMul) = Additive.ofMul b.toMul
    rw [hξ'pow k a.toMul, hk]
  let c' : Additive A → Additive A → Additive A :=
    fun x y => Additive.ofMul (c x.toMul y.toMul)
  have hc'mul : ∀ a b d : Additive A, c' (a + b) d = c' a d + c' b d := by
    intro a b d
    have h1 : (a + b).toMul = a.toMul * b.toMul := rfl
    show Additive.ofMul (c (a + b).toMul d.toMul)
        = Additive.ofMul (c a.toMul d.toMul * c b.toMul d.toMul)
    rw [h1, hmul a.toMul b.toMul d.toMul]
  have hc'mul' : ∀ a b d : Additive A, c' a (b + d) = c' a b + c' a d := by
    intro a b d
    have h1 : (b + d).toMul = b.toMul * d.toMul := rfl
    show Additive.ofMul (c a.toMul (b + d).toMul)
        = Additive.ofMul (c a.toMul b.toMul * c a.toMul d.toMul)
    rw [h1, hmul' a.toMul b.toMul d.toMul]
  have hc'alt : ∀ a : Additive A, c' a a = 0 := by
    intro a
    show Additive.ofMul (c a.toMul a.toMul) = Additive.ofMul (1 : A)
    rw [halt a.toMul]
  have hc'eq : ∀ a b : Additive A, ξ' (c' a b) = c' (ξ' a) (ξ' b) := by
    intro a b
    show Additive.ofMul (ξ (c a.toMul b.toMul))
        = Additive.ofMul (c (ξ a.toMul) (ξ b.toMul))
    rw [heq a.toMul b.toMul]
  have key : ∀ a b : Additive A, c' a b = 0 :=
    equivariant_bihom_trivial_zmod2 (V := Additive A) ξ' htrans' c' hc'mul hc'mul' hc'alt hc'eq
  intro a b
  have h1 : Additive.ofMul (c a b) = Additive.ofMul (1 : A) :=
    key (Additive.ofMul a) (Additive.ofMul b)
  exact h1

end Work.Higman
