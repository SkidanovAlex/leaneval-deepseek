import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Connected.Separation
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.Reconstruct.GammaDual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RankTheoryDeep



/-! ### Supporting lemmas -/

/-- **Finite-support elements are dense in a product.**  For any family of topological spaces
`X i`, the set of functions all but finitely many of whose coordinates equal `1` is dense in the
product.  Indeed a basic open set of the product topology only constrains finitely many
coordinates. -/
lemma dense_setOf_finite_ne_one {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, One (X i)] :
    Dense {f : (i : ι) → X i | {i | f i ≠ 1}.Finite} := by
  classical
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro f
  rw [mem_closure_iff]
  intro t ht hft
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp ht f hft
  have key : ∀ i ∈ I, (fun j => if j ∈ I then f j else 1) i ∈ u i := by
    intro i hi
    simp only [hi, ↓reduceIte]
    exact (hu i hi).2
  refine ⟨fun i => if i ∈ I then f i else 1, ?_, ?_⟩
  · apply hIu
    rw [Set.mem_pi]
    exact fun i hi => key i (by simpa using hi)
  · refine (Finset.finite_toSet I).subset ?_
    intro i hi
    by_contra hcon
    have hcon' : ¬ (i ∈ I) := by simpa using hcon
    exact hi (by simp [hcon'])

/-- A function on `ι` which is `1` outside a finset `s` is the product of the corresponding
coordinate functions `Pi.mulSingle i (f i)`. -/
lemma prod_mulSingle_of_eq_one_off {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, CommMonoid (M i)] (s : Finset ι) (f : ∀ i, M i) (h : ∀ i ∉ s, f i = 1) :
    ∏ i ∈ s, Pi.mulSingle i (f i) = f := by
  funext j
  rw [Finset.prod_apply]
  rw [Finset.prod_eq_single j (fun b _ hbj => Pi.mulSingle_eq_of_ne (Ne.symm hbj) (f b))
    (fun hj' => (Pi.mulSingle_eq_same j (f j)).trans (h j hj'))]
  rw [Pi.mulSingle_eq_same]

/-- A finite sum of additive homomorphisms is evaluated pointwise. -/
lemma addHom_sum_apply {M N ι : Type*} [AddZeroClass M] [AddCommMonoid N]
    (s : Finset ι) (f : ι → M →+ N) (y : M) : (∑ i ∈ s, f i) y = ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- **Continuous characters of a product of compact groups factor through a finite subproduct,
when all but finitely many factors have trivial dual.**

Let `A i` be a family of compact commutative topological groups, suppose that
`Dual (A i) ℓ = {f : Additive (A i) →+ ℤ_ℓ // Continuous f}` is **trivial for all but finitely
many** `i`, and let `χ : ∏_i A_i → ℤ_ℓ` be a continuous additive homomorphism.  Then `χ` is
trivial on the subgroup of families which are `1` on a *finite* set of coordinates: there is a
finite set `S` with `χ(x) = 0` for every `x` satisfying `x i = 1` for all `i ∈ S`.  (In fact the
proof gives the stronger identity `χ = ∑_{i ∈ S} χ_i` for the components
`χ_i(x) := χ(x^{(i)})`, where `x^{(i)}` is `x` at `i` and `1` elsewhere, i.e.
`χ` is determined by finitely many of its components.)

**The cofinite hypothesis is necessary**, and it is the arithmetic content of the application: the
function `χ(x) = ∑_n ℓ^n · x_n` on `∏_n ℤ_ℓ` (a convergent series, continuous because
`χ^{-1}(ℓ^N ℤ_ℓ)` contains the basic open set `{x : x_n ∈ ℓ^{N-n} ℤ_ℓ, n < N}`) is a
genuine infinite-support element of `Dual (∏_n ℤ_ℓ) ℓ`: for `S` finite and `m ∉ S`, the element
supported at `m` is trivial on `S` while `χ` takes the value `ℓ^m ≠ 0` there.  So the
*unconditional* version of this statement is false — see the refutation recorded in
`Submission/Work/RankTheoryDeep/exists_finset_support_of_dual_pi.lean`
(`NK.RankTheoryDeep.dualPi_not_conclusion`), left there by a colleague as the counterexample.

Proof.  For each `i`, `χ_i(a) := χ(a^{(i)})` is a continuous additive homomorphism `A_i → ℤ_ℓ`, i.e.
an element of `Dual (A_i) ℓ`; by hypothesis it is `0` for all `i` outside a finite set `T`.  Then
`ψ := χ - ∑_{i ∈ T} χ_i ∘ proj_i` vanishes on every coordinate subgroup, hence (by additivity) on
the dense subgroup of finitely supported families, hence is `0` since `ℤ_ℓ` is Hausdorff and `ψ` is
continuous.  So `S := T` works.

**Application** (the reason this is here): for `A_v = 𝒪_vˣ`, we have `Dual (𝒪_vˣ) ℓ = 0` for all but
the finitely many `v | ℓ` — this is
`NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne` (residue characteristic `≠ ℓ`) plus
the triviality of the dual of `ℝˣ` and `ℂˣ` (divisible or torsion).  Hence

  `Dual (∏_v 𝒪_vˣ) ℓ = ⊕_{v | ℓ} Dual (𝒪_vˣ) ℓ`,

of rank `∑_{v | ℓ} [K_v : ℚ_ℓ] = [K : ℚ]` (using the local unit structure at `v | ℓ`), and the exact
sequence `𝒪_Kˣ → ∏_v 𝒪_vˣ → C_K → Cl(K) → 0`
(`NK.GlobalCFT.IdeleClassGroup.local_global_exact_sequence`) bounds
`rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ)` — CoNF (10.3.20), the corrected residual
`NK.RankTheoryDeep.HausQuotRankFinite`.

Not vacuous: the statement is false without the cofinite hypothesis (counterexample above), and true
and useful with it (`A i = ℤ/ℓ` for all `i` satisfies the hypothesis and forces `χ = 0`). -/

theorem exists_finset_support_of_dual_pi_of_cofinite {ι : Type*} {A : ι → Type*}
    [∀ i, CommGroup (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    {ℓ : ℕ} [Fact ℓ.Prime]
    (h : ∀ᶠ i in Filter.cofinite, Subsingleton (NK.Reconstruct.Dual (A i) ℓ))
    (χ : NK.Reconstruct.Dual (∀ i, A i) ℓ) :
    ∃ S : Finset ι, ∀ x : ∀ i, A i, (∀ i ∈ S, x i = 1) →
      (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul x) = 0 := by
  classical
  -- Step 1: the exceptional set of coordinates with non-trivial dual is finite.
  obtain ⟨S, hS⟩ : ∃ S : Finset ι,
      ∀ i, i ∉ S → Subsingleton (NK.Reconstruct.Dual (A i) ℓ) := by
    obtain ⟨T, hT⟩ := (Filter.eventually_cofinite.mp h).exists_finset_coe
    refine ⟨T, fun i hi => ?_⟩
    by_contra hc
    have : i ∈ (T : Set ι) := by rw [hT]; exact hc
    exact hi (by simpa using this)
  -- Step 2: the components of `χ` and their extensions to the whole product.
  let χi : ∀ i, NK.Reconstruct.Dual (A i) ℓ := fun i =>
    NK.Reconstruct.dualMap ℓ (MonoidHom.mulSingle A i) (continuous_mulSingle i) χ
  let χc : ∀ i, Additive (∀ i, A i) →+ PadicInt ℓ := fun i =>
    (NK.Reconstruct.dualMap ℓ (Pi.evalMonoidHom A i) (continuous_apply i) (χi i) :
      NK.Reconstruct.Dual (∀ i, A i) ℓ)
  let ψ : Additive (∀ i, A i) →+ PadicInt ℓ :=
    (χ : Additive (∀ i, A i) →+ PadicInt ℓ) - ∑ i ∈ S, χc i
  have hψapply : ∀ y : Additive (∀ i, A i),
      ψ y = (χ : Additive (∀ i, A i) →+ PadicInt ℓ) y - ∑ j ∈ S, χc j y := by
    intro y
    rw [show ψ = (χ : Additive (∀ i, A i) →+ PadicInt ℓ) - ∑ i ∈ S, χc i from rfl]
    rw [AddMonoidHom.sub_apply, addHom_sum_apply]
  have hkey : ∀ (i : ι) (z : ∀ j, A j),
      χc i (Additive.ofMul z)
        = (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul (z i)) := by
    intro i z
    simp only [χc]
    rfl
  have hkey2 : ∀ (i : ι) (a : A i),
      (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul a)
        = (χ : Additive (∀ j, A j) →+ PadicInt ℓ)
            (Additive.ofMul (Pi.mulSingle (M := A) i a)) := by
    intro i a
    simp only [χi]
    rfl
  have hχi_zero : ∀ i, i ∉ S → ∀ a : A i,
      (χi i : Additive (A i) →+ PadicInt ℓ) (Additive.ofMul a) = 0 := by
    intro i hi a
    have h0 : χi i = (0 : NK.Reconstruct.Dual (A i) ℓ) :=
      @Subsingleton.elim (NK.Reconstruct.Dual (A i) ℓ) (hS i hi) _ _
    rw [h0]
    rfl
  -- Step 3: `ψ` vanishes on every coordinate subgroup.
  have hcoord : ∀ (i : ι) (a : A i),
      ψ (Additive.ofMul (Pi.mulSingle (M := A) i a)) = 0 := by
    intro i a
    rw [hψapply]
    by_cases hi : i ∈ S
    · rw [Finset.sum_eq_single i]
      · rw [hkey i (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_same, hkey2 i a]
        exact sub_self _
      · intro j hj hji
        rw [hkey j (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_of_ne hji a]
        simp
      · intro hi'; exact absurd hi hi'
    · rw [Finset.sum_eq_zero]
      · rw [← hkey2 i a, hχi_zero i hi a, sub_zero]
      · intro j hj
        have hji : j ≠ i := fun he => hi (he ▸ hj)
        rw [hkey j (Pi.mulSingle (M := A) i a), Pi.mulSingle_eq_of_ne hji a]
        simp
  -- Step 4: by additivity, `ψ` vanishes on all finitely supported elements.
  have hvan : ∀ z : ∀ i, A i, {i | z i ≠ 1}.Finite → ψ (Additive.ofMul z) = 0 := by
    intro z hz
    obtain ⟨T, hT⟩ := hz.exists_finset_coe
    have hz1 : ∀ i ∉ T, z i = 1 := by
      intro i hi
      by_contra hc
      have : i ∈ (T : Set ι) := by rw [hT]; exact hc
      exact hi (by simpa using this)
    have hprod : (∏ i ∈ T, Pi.mulSingle (M := A) i (z i)) = z :=
      prod_mulSingle_of_eq_one_off T z hz1
    have hsum : (∑ i ∈ T, Additive.ofMul (Pi.mulSingle (M := A) i (z i)))
        = Additive.ofMul z := by
      rw [← ofMul_prod, hprod]
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero (fun i _ => hcoord i (z i))
  -- Step 5: `ψ` is continuous, hence vanishes everywhere by density.
  have hcont : Continuous (fun z : ∀ i, A i => ψ (Additive.ofMul z)) := by
    have h1 : Continuous (fun z : ∀ i, A i =>
        (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)) := χ.2
    have h2 : Continuous (fun z : ∀ i, A i => ∑ j ∈ S, χc j (Additive.ofMul z)) := by
      apply continuous_finsetSum
      intro j hj
      have hjj : (fun z : ∀ i, A i => χc j (Additive.ofMul z))
          = fun z => (χi j : Additive (A j) →+ PadicInt ℓ) (Additive.ofMul (z j)) := by
        funext z
        exact hkey j z
      rw [hjj]
      exact (χi j).2.comp (continuous_apply j)
    have hfun : (fun z : ∀ i, A i => ψ (Additive.ofMul z))
        = fun z => (χ : Additive (∀ i, A i) →+ PadicInt ℓ) (Additive.ofMul z)
            - ∑ j ∈ S, χc j (Additive.ofMul z) := by
      funext z
      exact hψapply (Additive.ofMul z)
    rw [hfun]
    exact h1.sub h2
  have hmain : ∀ z : ∀ i, A i, ψ (Additive.ofMul z) = 0 := by
    have heq := Continuous.ext_on (dense_setOf_finite_ne_one (X := A)) hcont continuous_const
      (fun z hz => hvan z hz)
    intro z
    exact congrFun heq z
  -- Step 6: conclude.
  refine ⟨S, fun x hx => ?_⟩
  have hx0 : ψ (Additive.ofMul x) = 0 := hmain x
  rw [hψapply] at hx0
  have hsum0 : (∑ j ∈ S, χc j (Additive.ofMul x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hkey j x, hx j hj]
    simp
  rw [hsum0, sub_zero] at hx0
  exact hx0

end NK.RankTheoryDeep
