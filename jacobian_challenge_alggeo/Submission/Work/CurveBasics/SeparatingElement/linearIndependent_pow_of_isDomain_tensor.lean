import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.SeparatingElement

universe u

set_option linter.style.haveILetI false

open scoped TensorProduct in
/-- **Base change of linear independence.**  If `v : ι → K` is `k`-linearly independent, then the
family `1 ⊗ₜ vᵢ` is `L`-linearly independent in `L ⊗[k] K` for every `k`-algebra `L`.

The proof extends `v` to a `k`-basis of `K` (`Module.Basis.extend` applied to
`hv.linearIndepOn_id`), base changes that basis to an `L`-basis of `L ⊗[k] K`
(`Module.Basis.baseChange`), and restricts along the inclusion of `ι` into the index set of the
extended basis. -/
theorem linearIndependent_tmul_one {k L K : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup K] [Module k K] {ι : Type*} {v : ι → K} (hv : LinearIndependent k v) :
    LinearIndependent L (fun i => (1 : L) ⊗ₜ[k] v i) := by
  let s : Set K := Set.range v
  let hs : LinearIndepOn k id s := hv.linearIndepOn_id
  let f : ι → hs.extend (Set.subset_univ s) :=
    fun i => ⟨v i, Module.Basis.subset_extend hs ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun i j hij =>
    hv.injective (by simpa [f] using congrArg Subtype.val hij)
  have hb : ∀ i, (Module.Basis.extend hs) (f i) = v i := fun i => by
    simp [f, Module.Basis.coe_extend]
  have h := ((Module.Basis.extend hs).baseChange L).linearIndependent.comp f hf
  rw [show (fun i => (1 : L) ⊗ₜ[k] v i)
      = ((Module.Basis.extend hs).baseChange L) ∘ f from ?_]
  · exact h
  · funext i
    simp only [Function.comp_apply, Module.Basis.baseChange_apply, hb]

open scoped TensorProduct in
/-- **`p`-th powers of a `k`-linearly independent family in a field `K` stay `k`-linearly
independent when `K ⊗[k] L` is a domain for the field extension `L = AlgebraicClosure k`.**

Writing `L = AlgebraicClosure k`, the hypothesis `IsDomain (K ⊗[k] L)` says that `K` is "regular"
over `k`.  Pick `xᵢ ∈ L` with `xᵢ ^ p = algebraMap k L (lᵢ)` for each coefficient of a supposed
`k`-linear relation `∑ lᵢ • vᵢ^p = 0`, and consider `y = ∑ xᵢ ⊗ₜ vᵢ ∈ L ⊗[k] K`.  Then
`y ^ p = ∑ xᵢ^p ⊗ₜ vᵢ^p = ∑ algebraMap k L lᵢ ⊗ₜ vᵢ^p = 1 ⊗ₜ (∑ lᵢ • vᵢ^p) = 0`, so `y = 0`
because `L ⊗[k] K` is a domain (move the hypothesis across with `Algebra.TensorProduct.comm`).
On the other hand `k`-linear independence of the `vᵢ` upgrades to `L`-linear independence of the
`1 ⊗ₜ vᵢ` (base change of linear independence along `k → L`, e.g. `Module.Basis.tensorProduct`
applied to `Module.Basis.singleton` and a basis of `K` extending the `vᵢ`), so all coefficients
`xᵢ` vanish, whence `lᵢ = xᵢ^p = 0`.

Useful facts: `IsAlgClosed.exists_pow_nat_eq`, `CharP.of_ringHom_of_ne_zero`,
`sum_pow_char`, `TensorProduct.tmul_mul_tmul`, `Finsupp.mapRange`.

The intended proof works with `linearIndependent_iff` / `LinearIndependent` unfolded as
injectivity of `Finsupp.linearCombination`.) -/
theorem linearIndependent_pow_of_isDomain_tensor {k K : Type u} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (hdom : IsDomain (K ⊗[k] AlgebraicClosure k))
    {ι : Type*} {v : ι → K} (hv : LinearIndependent k v) :
    LinearIndependent k (fun i => (v i)^p) := by
  classical
  -- Move the domain hypothesis to the tensor product written with `L` on the left.
  haveI hdomI := hdom
  haveI hdom' : IsDomain (AlgebraicClosure k ⊗[k] K) :=
    MulEquiv.isDomain (K ⊗[k] AlgebraicClosure k)
      (Algebra.TensorProduct.comm k K (AlgebraicClosure k)).toRingEquiv.symm
  -- The tensor product is a `k`-algebra of characteristic `p`.
  haveI hck : CharP k p := (expChar_prime_iff k hp).mp inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hct : CharP (AlgebraicClosure k ⊗[k] K) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k _) p hp.ne_zero
  haveI het : ExpChar (AlgebraicClosure k ⊗[k] K) p := expChar_prime _ p
  rw [linearIndependent_iff]
  intro l hl
  -- Rewrite the given relation as a `Finset` sum.
  have hl' : ∑ i ∈ l.support, l i • (v i)^p = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
    exact hl
  -- Choose `p`-th roots in the algebraic closure.
  let root : k → AlgebraicClosure k := fun c =>
    Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) c) hp.pos)
  have hroot : ∀ c, (root c)^p = algebraMap k (AlgebraicClosure k) c := fun c =>
    Classical.choose_spec
      (IsAlgClosed.exists_pow_nat_eq (algebraMap k (AlgebraicClosure k) c) hp.pos)
  have hroot0 : root 0 = 0 := by
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [hroot, map_zero]
  -- The coefficient family in `L` supported on `l.support`.
  let X : ι →₀ AlgebraicClosure k :=
    Finsupp.onFinset l.support (fun i => root (l i)) (fun i hi => by
      rw [Finsupp.mem_support_iff]
      intro h
      exact hi (by rw [h, hroot0]))
  have hX : ∀ i, X i = root (l i) := fun i => Finsupp.onFinset_apply
  have hXsupp : X.support ⊆ l.support := Finsupp.support_onFinset_subset
  -- Base change of the linear independence of `v`.
  have hw : LinearIndependent (AlgebraicClosure k)
      (fun i => (1 : AlgebraicClosure k) ⊗ₜ[k] v i) := linearIndependent_tmul_one hv
  -- The powers of the individual terms.
  have hterm : ∀ i ∈ l.support, ((X i) • ((1 : AlgebraicClosure k) ⊗ₜ[k] v i))^p
      = (1 : AlgebraicClosure k) ⊗ₜ[k] (l i • (v i)^p) := by
    intro i _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [Algebra.TensorProduct.tmul_pow]
    rw [hX i, hroot (l i)]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  -- Replace the `Finsupp` sum by a sum over `l.support`.
  have hsplit : Finsupp.linearCombination (AlgebraicClosure k)
        (fun i => (1 : AlgebraicClosure k) ⊗ₜ[k] v i) X
      = ∑ i ∈ l.support, X i • ((1 : AlgebraicClosure k) ⊗ₜ[k] v i) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_subset hXsupp ?_
    intro i _ hiX
    rw [Finsupp.mem_support_iff, not_not] at hiX
    rw [hiX, zero_smul]
  -- The `p`-th power of the linear combination vanishes.
  have hsum : (∑ i ∈ l.support, X i • ((1 : AlgebraicClosure k) ⊗ₜ[k] v i))^p = 0 := by
    rw [sum_pow_char]
    rw [Finset.sum_congr rfl hterm]
    rw [← TensorProduct.tmul_sum]
    rw [hl']
    simp
  have hy : Finsupp.linearCombination (AlgebraicClosure k)
      (fun i => (1 : AlgebraicClosure k) ⊗ₜ[k] v i) X = 0 := by
    apply (pow_eq_zero_iff hp.ne_zero).mp
    rw [hsplit]
    exact hsum
  -- Conclude with the `L`-linear independence of the base changed family.
  rw [linearIndependent_iff] at hw
  have hX0 : X = 0 := hw X hy
  ext i
  have hXi : X i = 0 := by simp [hX0]
  rw [hX i] at hXi
  have h2 : algebraMap k (AlgebraicClosure k) (l i) = 0 := by
    rw [← hroot (l i), hXi, zero_pow hp.ne_zero]
  exact (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)) (by simpa using h2)

end Work.CurveBasics.SeparatingElement
