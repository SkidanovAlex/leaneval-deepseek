import Mathlib
import Submission.Work.Higman.equivariant_bihom_trivial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

/-- **Auxiliary form of Gorenstein–Thompson (Higman 1963, Lemma 4).**  Let `V` be a finite
`ZMod 2`-module and `ξ` an automorphism of `V` permuting the nonzero vectors transitively.  Then
every `ξ`-equivariant alternating biadditive map `θ : V → V → V` is identically zero.

This is the special case of `Work.Higman.equivariant_bihom_trivial` in which the target of the
pairing is `ξ`-isomorphic to the source, transported from the `ZMod 2`-module language to the
`Multiplicative` (elementary abelian group) language. -/
theorem equivariant_alt_self_trivial {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    (θ : V → V → V)
    (h1 : ∀ a b d : V, θ (a + b) d = θ a d + θ b d)
    (h2 : ∀ a b d : V, θ a (b + d) = θ a b + θ a d)
    (halt : ∀ a : V, θ a a = 0)
    (heq : ∀ a b : V, θ (ξ a) (ξ b) = ξ (θ a b)) :
    ∀ a b : V, θ a b = 0 := by
  -- `V` has exponent two
  have hxx : ∀ x : V, x + x = 0 := by
    intro x
    have h : (2 : ZMod 2) • x = x + x := two_smul (ZMod 2) x
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  -- `ξ` as a multiplicative automorphism of `Multiplicative V`
  let ξM : MulAut (Multiplicative V) := ξ.toAddEquiv.toMultiplicative
  have hM2 : ∀ a : Multiplicative V, a * a = 1 := by
    intro a
    exact hxx a.toAdd
  have hpow : ∀ (k : ℕ) (a : Multiplicative V),
      (ξM ^ k) a = Multiplicative.ofAdd ((ξ ^ k) a.toAdd) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
        intro a
        rw [pow_succ]
        change (ξM ^ k) (ξM a) = _
        have ha : ξM a = Multiplicative.ofAdd (ξ a.toAdd) := rfl
        rw [ha, ih]
        congr 1
  have htransM : ∀ a b : Multiplicative V, a ≠ 1 → b ≠ 1 → ∃ k, (ξM ^ k) a = b := by
    intro a b ha hb
    have ha' : a.toAdd ≠ 0 := by simpa using ha
    have hb' : b.toAdd ≠ 0 := by simpa using hb
    obtain ⟨k, hk⟩ := htrans a.toAdd b.toAdd ha' hb'
    exact ⟨k, by rw [hpow k a, hk]; rfl⟩
  let cm : Multiplicative V → Multiplicative V → Multiplicative V :=
    fun a b => Multiplicative.ofAdd (θ a.toAdd b.toAdd)
  have hcm1 : ∀ a b d : Multiplicative V, cm (a * b) d = cm a d * cm b d := by
    intro a b d
    show Multiplicative.ofAdd (θ (a.toAdd + b.toAdd) d.toAdd)
        = Multiplicative.ofAdd (θ a.toAdd d.toAdd) * Multiplicative.ofAdd (θ b.toAdd d.toAdd)
    rw [h1, ofAdd_add]
  have hcm2 : ∀ a b d : Multiplicative V, cm a (b * d) = cm a b * cm a d := by
    intro a b d
    show Multiplicative.ofAdd (θ a.toAdd (b.toAdd + d.toAdd))
        = Multiplicative.ofAdd (θ a.toAdd b.toAdd) * Multiplicative.ofAdd (θ a.toAdd d.toAdd)
    rw [h2, ofAdd_add]
  have hcmalt : ∀ a : Multiplicative V, cm a a = 1 := by
    intro a
    show Multiplicative.ofAdd (θ a.toAdd a.toAdd) = 1
    rw [halt]
    rfl
  have hcmeq : ∀ a b : Multiplicative V, ξM (cm a b) = cm (ξM a) (ξM b) := by
    intro a b
    show Multiplicative.ofAdd (ξ (θ a.toAdd b.toAdd))
        = Multiplicative.ofAdd (θ (ξ a.toAdd) (ξ b.toAdd))
    rw [← heq]
  have key := equivariant_bihom_trivial hM2 ξM htransM cm hcm1 hcm2 hcmalt hcmeq
  intro a b
  have h := key (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  exact Multiplicative.ofAdd.injective (by simpa [cm] using h)

/-- Gorenstein–Thompson (Higman 1963, Lemma 4), module form: if an `𝔽₂`-linear automorphism `ξ`
of `V` is transitive on `V \ {0}`, `η` is an `𝔽₂`-linear automorphism of `W`, and `β` is a
non-zero alternating `ξ`-equivariant biadditive map `V → V → W`, then no `𝔽₂`-linear isomorphism
`σ : V ≃ W` satisfies `σ (ξ v) = η (σ v)`. -/
theorem no_equivariant_linearEquiv
    {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ξ : V ≃ₗ[ZMod 2] V) (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    (η : W ≃ₗ[ZMod 2] W) (β : V → V → W)
    (hβ1 : ∀ a b d : V, β (a + b) d = β a d + β b d)
    (hβ2 : ∀ a b d : V, β a (b + d) = β a b + β a d)
    (halt : ∀ a : V, β a a = 0)
    (heq : ∀ a b : V, β (ξ a) (ξ b) = η (β a b))
    (hne : ∃ a b : V, β a b ≠ 0) :
    ¬ ∃ σ : V ≃ₗ[ZMod 2] W, ∀ v : V, σ (ξ v) = η (σ v) := by
  rintro ⟨σ, hσ⟩
  -- the two automorphisms are intertwined by `σ.symm` in the reverse direction
  have hsymm : ∀ w : W, σ.symm (η w) = ξ (σ.symm w) := by
    intro w
    apply σ.injective
    rw [LinearEquiv.apply_symm_apply, hσ (σ.symm w), LinearEquiv.apply_symm_apply]
  -- transferring `β` back along `σ` produces an alternating biadditive `ξ`-equivariant self-map
  have hcore : ∀ a b : V, σ.symm (β a b) = 0 :=
    equivariant_alt_self_trivial ξ htrans (fun a b => σ.symm (β a b))
      (by intro a b d; rw [hβ1, map_add])
      (by intro a b d; rw [hβ2, map_add])
      (by intro a; rw [halt, map_zero])
      (by intro a b; rw [heq, hsymm (β a b)])
  obtain ⟨a, b, hab⟩ := hne
  exact hab (σ.symm.injective (by rw [hcore a b, map_zero]))

end Work.Higman
