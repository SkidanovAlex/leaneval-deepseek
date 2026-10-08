import Mathlib
import Submission.Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Higman.MSA

/-- **Higman's Lemma 8, cardinality bound (abstract form).**

Let `V` be a finite abelian group of exponent two (equivalently, an `𝔽₂`-vector space) and
`xiV` an automorphism with `xiV ^ (2 ^ n - 1) = 1`.  If the only `xiV`-invariant subgroups of
`V` are `⊥` and `⊤` (i.e. `V` is a simple `𝔽₂[xiV]`-module), then `|V| ≤ 2 ^ n`.

Route: transport the multiplicative data along `Additive V`, where the exponent-two hypothesis
turns `V` into an `𝔽₂`-module (via `AddCommGroup.zmodModule`); `xiV` becomes an `𝔽₂`-linear
equivalence `ζV` and the hypothesis on subgroups becomes the hypothesis on submodules (a
subgroup is `xiV`-invariant iff the corresponding submodule is `ζV`-invariant; the equality
`K.map xiV = K` is equivalent to invariance because `xiV` is injective and `K` is finite).
Then `Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one` gives
`finrank 𝔽₂ V ∣ n`, whence `finrank 𝔽₂ V ≤ n` and `|V| = 2 ^ finrank 𝔽₂ V ≤ 2 ^ n`. -/
theorem l8_card_le {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v * v = 1) (xiV : V ≃* V) {n : ℕ} (hn : 1 ≤ n)
    (hxi : xiV ^ (2 ^ n - 1) = 1)
    (hirr : ∀ K : Subgroup V, K.map xiV.toMonoidHom = K → K = ⊥ ∨ K = ⊤) :
    Nat.card V ≤ 2 ^ n := by
  classical
  -- `𝔽₂` has exactly two elements.
  have hz2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  -- The exponent-two hypothesis makes `Additive V` an `𝔽₂`-vector space.
  haveI hmod : Module (ZMod 2) (Additive V) :=
    AddCommGroup.zmodModule fun x => by
      rw [show (2 : ℕ) • x = x + x from two_nsmul x]
      have hx : x + x = Additive.ofMul ((Additive.toMul x) * (Additive.toMul x)) := rfl
      rw [hx, hV2 (Additive.toMul x)]
      rfl
  -- `xiV` as an `𝔽₂`-linear equivalence of `Additive V`.
  let ζV : Additive V ≃ₗ[ZMod 2] Additive V :=
    { toFun := fun x => Additive.ofMul (xiV (Additive.toMul x))
      invFun := fun x => Additive.ofMul (xiV.symm (Additive.toMul x))
      left_inv := fun x => by
        show Additive.ofMul (xiV.symm (xiV (Additive.toMul x))) = x
        rw [MulEquiv.symm_apply_apply, ofMul_toMul]
      right_inv := fun x => by
        show Additive.ofMul (xiV (xiV.symm (Additive.toMul x))) = x
        rw [MulEquiv.apply_symm_apply, ofMul_toMul]
      map_add' := fun x y => by
        show Additive.ofMul (xiV (Additive.toMul (x + y)))
          = Additive.ofMul (xiV (Additive.toMul x)) + Additive.ofMul (xiV (Additive.toMul y))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun c x => by
        rcases hz2 c with rfl | rfl <;> simp }
  -- `ζV` computes the same powers as `xiV`.
  have hζpow : ∀ (k : ℕ) (x : Additive V),
      (ζV ^ k) x = Additive.ofMul ((xiV ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero]; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', LinearEquiv.mul_apply, ih]
      show Additive.ofMul (xiV (Additive.toMul (Additive.ofMul ((xiV ^ k) (Additive.toMul x)))))
        = Additive.ofMul ((xiV ^ (k + 1)) (Additive.toMul x))
      rw [toMul_ofMul, pow_succ']
      rfl
  have hζ : ζV ^ (2 ^ n - 1) = 1 := by
    ext x
    rw [hζpow, hxi]
    simp
  by_cases hsub : Subsingleton V
  · -- The trivial group: `|V| = 1 ≤ 2 ^ n`.
    have h1 : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [h1]
    exact Nat.one_le_pow n 2 (by norm_num)
  · -- The non-trivial case: reduce to the submodule form of the irreducibility hypothesis.
    haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    haveI hntA : Nontrivial (Additive V) := inferInstanceAs (Nontrivial V)
    have hirr' : ∀ U : Submodule (ZMod 2) (Additive V),
        (∀ v ∈ U, ζV v ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      -- the subgroup of `V` underlying the submodule `U`
      let K : Subgroup V := AddSubgroup.toSubgroup' U.toAddSubgroup
      have hmem : ∀ v : V, v ∈ K ↔ Additive.ofMul v ∈ U :=
        fun v => AddSubgroup.mem_toSubgroup' U.toAddSubgroup v
      have hKinv : ∀ v ∈ K, xiV v ∈ K := by
        intro v hv
        rw [hmem] at hv ⊢
        have h := hU (Additive.ofMul v) hv
        rwa [show ζV (Additive.ofMul v) = Additive.ofMul (xiV v) from rfl] at h
      -- invariance upgrades to `xiV`-stability, since `xiV` is injective
      have hKfix : K.map xiV.toMonoidHom = K := by
        have hle : K.map xiV.toMonoidHom ≤ K := by
          rintro x ⟨y, hy, rfl⟩
          exact hKinv y hy
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [Subgroup.card_map_of_injective xiV.injective]
      rcases hirr K hKfix with h | h
      · left
        rw [Submodule.eq_bot_iff]
        intro x hx
        have hxK : Additive.toMul x ∈ K := (hmem _).mpr (by rwa [ofMul_toMul])
        rw [h, Subgroup.mem_bot] at hxK
        show x = 0
        rw [← ofMul_toMul x, hxK, ofMul_one]
      · right
        rw [Submodule.eq_top_iff']
        intro x
        have hxt : Additive.toMul x ∈ K := by rw [h]; exact Subgroup.mem_top _
        have hxU := (hmem _).mp hxt
        rwa [ofMul_toMul] at hxU
    -- `finrank 𝔽₂ V ∣ n`, hence `finrank 𝔽₂ V ≤ n`.
    have hdvd : Module.finrank (ZMod 2) (Additive V) ∣ n :=
      Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one ζV hn hζ hirr'
    have hfl : Module.finrank (ZMod 2) (Additive V) ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      rw [Nat.card_zmod] at h
      exact h
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) hfl

end Work.Higman.MSA
