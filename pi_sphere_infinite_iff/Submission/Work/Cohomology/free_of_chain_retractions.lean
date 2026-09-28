import Mathlib

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false


namespace Work.Cohomology

open DirectSum

/-- Transport `Module.Free` across the (unique) `ℤ`-module structure on a fixed additive group. -/
lemma Module.Free.of_module_eq {M : Type*} [AddCommGroup M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Free ℤ M _ _ m₁) : @Module.Free ℤ M _ _ m₂ := by
  rw [Subsingleton.elim m₁ m₂] at h
  exact h

/-- The canonical inclusion `V (k+1) ↪ M`, as a `ℤ`-linear map.  (We build it by hand because the
module structure on `↥(V (k+1))` appearing in the hypothesis on the retractions is the canonical
integer module structure, which is propositionally — but not definitionally — the submodule
structure.) -/
def chainIncl {M : Type*} [AddCommGroup M] [Module ℤ M] (V : ℕ → Submodule ℤ M) (k : ℕ) :
    ↥(V (k+1)) →ₗ[ℤ] M :=
  { toFun := fun x => (x : M)
    map_add' := by intro a b; rfl
    map_smul' := by
      intro c a
      have hmod : (AddCommGroup.toIntModule ↥(V (k+1))) = (V (k+1)).module :=
        Subsingleton.elim _ _
      rw [hmod]
      exact Submodule.coe_smul c a }

@[simp] lemma chainIncl_apply {M : Type*} [AddCommGroup M] [Module ℤ M] (V : ℕ → Submodule ℤ M)
    (k : ℕ) (x : ↥(V (k+1))) : chainIncl V k x = (x : M) := rfl

/-- Given an increasing chain of submodules `V 0 ≤ V 1 ≤ ⋯` with `⨆ n, V n = ⊤`, whose `0`-th term
is free and which is split at each step (`r n : V (n+1) → V n` retracts the inclusion) with free
kernels, the ambient module is free.  Indeed `M ≅ V 0 ⊕ ⨁ₙ ker (r n)`. -/
theorem free_of_chain_retractions {M : Type*} [AddCommGroup M] [Module ℤ M]
    (V : ℕ → Submodule ℤ M) (hmono : ∀ n, V n ≤ V (n+1))
    (hsup : ⨆ n, V n = ⊤)
    (hV0 : Module.Free ℤ ↥(V 0))
    (r : ∀ n, ↥(V (n+1)) →ₗ[ℤ] ↥(V n))
    (hr : ∀ n (x : ↥(V n)), r n ⟨x.1, hmono n x.2⟩ = x)
    (hker : ∀ n, Module.Free ℤ ↥(LinearMap.ker (r n))) :
    Module.Free ℤ M := by
  classical
  -- The "new" summands: `A 0 = V 0`, `A (k+1) = ker (r k)` viewed in `M`.
  let A : ℕ → Submodule ℤ M := fun n => match n with
    | 0 => V 0
    | k+1 => (LinearMap.ker (r k)).map (chainIncl V k)
  have hA0 : A 0 = V 0 := rfl
  have hAsucc : ∀ k, A (k+1) = (LinearMap.ker (r k)).map (chainIncl V k) := fun k => rfl
  -- Use the submodule module structures on the `↥(A i)` (this is what `coeLinearMap` uses).
  letI : ∀ i, Module ℤ ↥(A i) := fun i => (A i).module
  letI : Module ℤ (⨁ i : ℕ, ↥(A i)) := instModule
  -- monotonicity of the chain
  have hVmono : Monotone V := monotone_nat_of_le_succ hmono
  -- `A i ≤ V i`
  have hAleV : ∀ i, A i ≤ V i := by
    intro i
    cases i with
    | zero => exact le_rfl
    | succ k =>
      rw [hAsucc k, Submodule.map_le_iff_le_comap]
      intro x _
      simpa using x.2
  -- `V n` and `A (n+1)` are complementary inside `V (n+1)`
  have hdisj : ∀ n, V n ⊓ A (n+1) = ⊥ := by
    intro n
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨hxn, hxA⟩ := hx
    change x ∈ (LinearMap.ker (r n)).map (chainIncl V n) at hxA
    rw [Submodule.mem_map] at hxA
    obtain ⟨w, hw, hwx⟩ := hxA
    have hw1 : (w : M) = x := hwx
    have hweq : w = (⟨x, hmono n hxn⟩ : ↥(V (n+1))) := Subtype.ext hw1
    have hzero : r n (⟨x, hmono n hxn⟩ : ↥(V (n+1))) = 0 := by
      rw [← hweq]; exact hw
    rw [hr n ⟨x, hxn⟩] at hzero
    simpa using congrArg Subtype.val hzero
  have hsupA' : ∀ n, V n ⊔ A (n+1) = V (n+1) := by
    intro n
    apply le_antisymm
    · rw [sup_le_iff]
      exact ⟨hmono n, hAleV (n+1)⟩
    · intro y hy
      rw [Submodule.mem_sup]
      set y' : ↥(V (n+1)) := ⟨y, hy⟩ with hy'def
      set a : ↥(V n) := r n y' with hadef
      refine ⟨(a : M), a.2, y - (a : M), ?_, ?_⟩
      · -- `y - a ∈ A (n+1)`
        set w : ↥(V (n+1)) := y' - ⟨(a : M), hmono n a.2⟩ with hwdef
        have hker : w ∈ LinearMap.ker (r n) := by
          rw [hwdef, LinearMap.mem_ker, map_sub, ← hadef, hr n a, sub_self]
        have hmem : (w : M) ∈ A (n+1) := by
          rw [hAsucc n]
          exact Submodule.mem_map.mpr ⟨w, hker, rfl⟩
        have hwcoe : (w : M) = y - (a : M) := by rw [hwdef]; rfl
        rwa [hwcoe] at hmem
      · show (a : M) + (y - (a : M)) = y
        abel
  -- `⨆ i, A i = ⊤`
  have hsupA : (⨆ i, A i) = ⊤ := by
    have hle : ∀ n, V n ≤ ⨆ i, A i := by
      intro n
      induction n with
      | zero => rw [← hA0]; exact le_iSup A 0
      | succ n ih =>
        calc V (n+1) = V n ⊔ A (n+1) := (hsupA' n).symm
          _ ≤ (⨆ i, A i) ⊔ (⨆ i, A i) := sup_le_sup ih (le_iSup A (n+1))
          _ = ⨆ i, A i := sup_idem _
    refine le_antisymm le_top ?_
    rw [← hsup]
    exact iSup_le hle
  -- The linear map sending a finitely supported family to its sum.
  let L := DirectSum.coeLinearMap A
  have hsingle : ∀ (i : ℕ) (y : ↥(A i)), L (DFinsupp.single i y) = (y : M) := by
    intro i y
    change DirectSum.coeLinearMap A (DFinsupp.single i y) = (y : M)
    rw [show (DFinsupp.single i y : Π₀ j : ℕ, ↥(A j)) = DirectSum.of (fun j => ↥(A j)) i y from rfl,
      DirectSum.coeLinearMap_of]
  have Lapply : ∀ (x : Π₀ i : ℕ, ↥(A i)), L x = ∑ i ∈ x.support, (x i : M) := by
    intro x
    change DirectSum.coeLinearMap A x = _
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum]
  -- `L` is injective
  have hinjL : Function.Injective L := by
    have key : ∀ B, ∀ x : Π₀ i : ℕ, ↥(A i),
        (∀ i, B < i → x i = 0) → L x = 0 → x = 0 := by
      intro B
      induction B with
      | zero =>
        intro x hx hL
        have hxeq : x = DFinsupp.single 0 (x 0) := by
          ext i
          rcases eq_or_ne i 0 with rfl | hi
          · simp
          · rw [DFinsupp.single_eq_of_ne hi, hx i (Nat.pos_of_ne_zero hi)]
        rw [hxeq] at hL
        rw [hsingle] at hL
        have h0 : x 0 = 0 := by
          exact Subtype.ext (by simpa using hL)
        rw [hxeq, h0]; simp
      | succ B ih =>
        intro x hx hL
        set c : ↥(A (B+1)) := x (B+1) with hcdef
        set x' : Π₀ i : ℕ, ↥(A i) := x - DFinsupp.single (B+1) c with hx'def
        have hx' : ∀ i, B < i → x' i = 0 := by
          intro i hi
          rcases eq_or_ne i (B+1) with rfl | hne
          · rw [hx'def, DFinsupp.sub_apply, DFinsupp.single_eq_same, hcdef]; simp
          · have hlt : B+1 < i := by omega
            rw [hx'def, DFinsupp.sub_apply, DFinsupp.single_eq_of_ne hne, sub_zero, hx i hlt]
        have hLx' : L x' = -((c : M)) := by
          rw [hx'def, map_sub, hL, hsingle]
          simp
        have hLmem : L x' ∈ V B := by
          rw [Lapply]
          refine Submodule.sum_mem (V B) (fun i hi => ?_)
          rw [DFinsupp.mem_support_iff] at hi
          have hle : i ≤ B := by
            by_contra hcon
            exact hi (hx' i (not_le.mp hcon))
          exact (hAleV i).trans (hVmono hle) (x' i).2
        have hcmem : (c : M) ∈ V B := by
          have hneg : -((c : M)) ∈ V B := by rw [← hLx']; exact hLmem
          simpa using neg_mem hneg
        have hc0 : c = 0 := by
          have hmem : (c : M) ∈ V B ⊓ A (B+1) := ⟨hcmem, c.2⟩
          rw [hdisj B, Submodule.mem_bot] at hmem
          exact Subtype.ext hmem
        have hx'0 : x' = 0 := ih x' hx' (by rw [hLx', hc0]; simp)
        have hxeq : x' = x := by rw [hx'def, hc0]; simp
        rw [← hxeq]; exact hx'0
    intro x y hxy
    have h : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hb : ∀ i, (x - y).support.sup id < i → (x - y) i = 0 := by
      intro i hi
      by_contra hne
      exact absurd (Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hne)) (not_le.mpr hi)
    have hz := key ((x - y).support.sup id) (x - y) hb h
    rwa [sub_eq_zero] at hz
  -- `L` is also surjective, hence `IsInternal A`
  have hsurjL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    change LinearMap.range (DirectSum.coeLinearMap A) = ⊤
    rw [DirectSum.range_coeLinearMap, hsupA]
  have hInt : IsInternal A := ⟨hinjL, hsurjL⟩
  -- each `A i` is free
  have hfreeA : ∀ i, Module.Free ℤ ↥(A i) := by
    intro i
    cases i with
    | zero => exact Module.Free.of_module_eq hV0
    | succ k =>
      letI : Module ℤ ↥(A (k+1)) := (A (k+1)).module
      have he : ↥(LinearMap.ker (r k)) ≃ₗ[ℤ] ↥(A (k+1)) :=
        Submodule.equivMapOfInjective (chainIncl V k)
          (fun a b hab => Subtype.ext (by simpa using hab)) (LinearMap.ker (r k))
      exact Module.Free.of_equiv' (Module.Free.of_module_eq (hker k)) he
  -- assemble
  haveI : ∀ i, Module.Free ℤ ↥(A i) := hfreeA
  have hfree := Module.Free.directSum ℤ (fun i => ↥(A i))
  exact Module.Free.of_equiv' hfree
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hInt)

end Work.Cohomology

