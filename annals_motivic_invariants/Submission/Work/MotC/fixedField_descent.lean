import Mathlib
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

namespace Work.MotC

open IntermediateField

/-- **Descent along the cyclic quintic automorphism.**
Let `L/𝕜` be a cyclic extension of degree `5` with generator `gen`, let `𝕜 → L → K` be a tower of
fields, and let `α` be a `𝕜`-automorphism of `K` with `α ^ 5 = 1`, `α ≠ 1`, whose restriction to
`L` is `gen`.  Then the fixed field `K ^ ⟨α⟩` is linearly disjoint from `L` over `𝕜`, it generates
`K` together with the image of `L`, and `K` is of degree `5` over it.

The degree statement is Artin's theorem in the form that applies to an arbitrary (not necessarily
finite dimensional) field extension (`FixedPoints.finrank_eq_card`), the generation statement is
the prime-degree argument (`[K : K^α] = 5` and `F ⊔ L ≠ F`), and linear disjointness is proved by
identifying `K` with the `F`-span of `L`, using that a finite dimensional domain over a field is a
field. -/
theorem fixedField_descent {𝕜 : Type} [Field 𝕜] (Cyc : Work.TorsorExistence.CyclicExtension 𝕜 5)
    (K : Type*) [Field K] [Algebra 𝕜 K] [Algebra Cyc.L K] [IsScalarTower 𝕜 Cyc.L K]
    (α : K ≃ₐ[𝕜] K) (h5 : α ^ 5 = 1) (hne : α ≠ 1)
    (hα : ∀ l : Cyc.L, α (algebraMap Cyc.L K l) = algebraMap Cyc.L K (Cyc.gen l)) :
    (IntermediateField.fixedField (Subgroup.zpowers α)).LinearDisjoint Cyc.L ∧
      IntermediateField.fixedField (Subgroup.zpowers α) ⊔
          (IsScalarTower.toAlgHom 𝕜 Cyc.L K).fieldRange = ⊤ ∧
        Module.finrank ↥(IntermediateField.fixedField (Subgroup.zpowers α)) K = 5 := by
  classical
  haveI hprime : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have horder : orderOf α = 5 := orderOf_eq_prime h5 hne
  have hxfin : IsOfFinOrder α := by
    rw [isOfFinOrder_iff_pow_eq_one]; exact ⟨5, by norm_num, h5⟩
  haveI hHfin : Fintype ↥(Subgroup.zpowers α) :=
    Fintype.ofEquiv (Fin (orderOf α)) (finEquivZPowers hxfin)
  have hcard : Nat.card ↥(Subgroup.zpowers α) = 5 := by rw [Nat.card_zpowers, horder]
  set F : IntermediateField 𝕜 K := IntermediateField.fixedField (Subgroup.zpowers α) with hFdef
  set f : Cyc.L →ₐ[𝕜] K := IsScalarTower.toAlgHom 𝕜 Cyc.L K with hf
  set L' : IntermediateField 𝕜 K := f.fieldRange with hL'def
  -- Artin's theorem: `K` has degree `5` over the fixed field of `α`
  have hfinF : Module.finrank ↥F K = 5 := by
    have h := FixedPoints.finrank_eq_card ↥(Subgroup.zpowers α) K
    rw [← Nat.card_eq_fintype_card, hcard] at h
    exact h
  haveI hFfd : FiniteDimensional ↥F K := Module.finite_of_finrank_pos (by rw [hfinF]; norm_num)
  have hα' : ∀ l : Cyc.L, α (f l) = f (Cyc.gen l) := fun l => by rw [hf]; exact hα l
  -- `L` is not contained in the fixed field
  have hex : ∃ x : K, x ∈ L' ∧ x ∉ F := by
    obtain ⟨l, hl⟩ : ∃ l : Cyc.L, l ∉ (⊥ : IntermediateField 𝕜 Cyc.L) := by
      by_contra h
      push Not at h
      have hbot : (⊥ : IntermediateField 𝕜 Cyc.L) = ⊤ :=
        SetLike.ext fun x => ⟨fun _ => IntermediateField.mem_top, fun _ => h x⟩
      have h1 : Module.finrank 𝕜 ↥(⊥ : IntermediateField 𝕜 Cyc.L) = 1 :=
        IntermediateField.finrank_eq_one_iff.mpr rfl
      rw [hbot, IntermediateField.finrank_top', Cyc.finrank_eq] at h1
      exact absurd h1 (by norm_num)
    refine ⟨f l, ?_, ?_⟩
    · rw [hL'def]; exact AlgHom.mem_fieldRange.mpr ⟨l, rfl⟩
    · intro hmem
      have hfix : α (f l) = f l := by
        have h' := (IntermediateField.mem_fixedField_iff (Subgroup.zpowers α) _).mp
          (by rw [← hFdef]; exact hmem) α (Subgroup.mem_zpowers α)
        simpa [hf] using h'
      have hgen : Cyc.gen l = l := by
        apply f.injective
        change f (Cyc.gen l) = f l
        rw [← hα' l]
        exact hfix
      have hmem_bot : l ∈ (⊥ : IntermediateField 𝕜 Cyc.L) := by
        rw [IntermediateField.mem_bot]
        refine (IsGalois.mem_range_algebraMap_iff_fixed (F := 𝕜) (E := Cyc.L) l).mpr ?_
        have hpow : ∀ k : ℕ, (Cyc.gen ^ k) l = l := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hgen, ih]
        intro g
        obtain ⟨k, hk⟩ := Cyc.gen_generator g
        rw [hk]
        exact hpow k
      exact hl hmem_bot
  obtain ⟨x₀, hx₀L, hx₀F⟩ := hex
  -- ## Step 2: `F · L = K`
  set M : IntermediateField 𝕜 K := F ⊔ L' with hMdef
  have hLM : L' ≤ M := le_sup_right
  have hMne : M ≠ F := fun h => hx₀F (h ▸ hLM hx₀L)
  have hMtop : M = ⊤ := by
    let M' : IntermediateField ↥F K :=
      M.toSubfield.toIntermediateField (fun x => (le_sup_left : F ≤ M) x.2)
    have hM'coe : (M' : Set K) = (M : Set K) := rfl
    have hM'ne : M' ≠ ⊥ := by
      intro hbot
      apply hMne
      have hc : (M : Set K) = (F : Set K) := by
        rw [← hM'coe, hbot, IntermediateField.coe_bot]
        ext x
        simp only [Set.mem_range]
        constructor
        · rintro ⟨y, rfl⟩; exact y.2
        · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
      refine SetLike.ext fun x => ⟨fun h => ?_, fun h => ?_⟩
      · show x ∈ (F : Set K); rw [← hc]; exact h
      · show x ∈ (M : Set K); rw [hc]; exact h
    -- the tower law `[K : F] = [M : F] * [K : M]`
    have hprod : Module.finrank ↥F ↥M' * Module.finrank ↥M' K = 5 := by
      rw [Module.finrank_mul_finrank, hfinF]
    have hne1 : Module.finrank ↥F ↥M' ≠ 1 :=
      fun h => hM'ne (IntermediateField.finrank_eq_one_iff.mp h)
    have hdvd : Module.finrank ↥F ↥M' ∣ 5 := ⟨Module.finrank ↥M' K, by rw [← hprod]⟩
    have ha : Module.finrank ↥F ↥M' = 5 := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 5) _ hdvd) with h | h
      · exact absurd h hne1
      · exact h
    have htop_sub : M'.toSubmodule = (⊤ : Submodule ↥F K) :=
      Submodule.eq_top_of_finrank_eq (S := M'.toSubmodule) (by
        show Module.finrank ↥F ↥M' = Module.finrank ↥F K
        rw [ha, hfinF])
    have hset : (M : Set K) = Set.univ := by
      rw [← hM'coe]
      simpa using congrArg (fun s : Submodule ↥F K => (s : Set K)) htop_sub
    refine SetLike.ext fun x => ⟨fun _ => IntermediateField.mem_top, fun _ => ?_⟩
    show x ∈ (M : Set K)
    rw [hset]
    exact Set.mem_univ x
  -- ## Step 3: the `F`-span of `L` is everything
  have hWtop : (⊤ : Submodule ↥F K) ≤ Submodule.span ↥F (L' : Set K) := by
    let W : Submodule ↥F K := Submodule.span ↥F (L' : Set K)
    have hmul : W * W ≤ W := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro x ⟨y, hy, z, hz, rfl⟩
      exact L'.mul_mem hy hz
    have hone : (1 : K) ∈ W := Submodule.subset_span L'.one_mem
    have hFmem : ∀ g : ↥F, (g : K) ∈ W := by
      intro g
      have h1 : (g : K) = g • (1 : K) := (mul_one _).symm
      rw [h1]
      exact Submodule.smul_mem W g hone
    let S : Subalgebra ↥F K :=
      { carrier := (W : Set K)
        mul_mem' := fun ha hb => hmul (Submodule.mul_mem_mul ha hb)
        one_mem' := hone
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        algebraMap_mem' := fun r => hFmem r }
    haveI hSdom : IsDomain ↥S := inferInstance
    haveI hSfin : FiniteDimensional ↥F ↥S := inferInstanceAs (FiniteDimensional ↥F ↥W)
    -- a finite dimensional domain over a field is a field
    have hfield : IsField ↥S := IsField.of_isDomain_of_finite ↥F ↥S
    let Wif' : IntermediateField ↥F K := S.toIntermediateField' hfield
    let Wif : IntermediateField 𝕜 K :=
      Wif'.toSubfield.toIntermediateField (fun a => by
        rw [IsScalarTower.algebraMap_apply 𝕜 ↥F K]
        exact Wif'.algebraMap_mem _)
    have hWifcoe : (Wif : Set K) = (W : Set K) := rfl
    have hFW : F ≤ Wif := by
      intro x hx
      change x ∈ (Wif : Set K)
      rw [hWifcoe]
      exact hFmem ⟨x, hx⟩
    have hLW : L' ≤ Wif := by
      intro x hx
      change x ∈ (Wif : Set K)
      rw [hWifcoe]
      exact Submodule.subset_span hx
    have hle : F ⊔ L' ≤ Wif := sup_le hFW hLW
    rw [← hMdef, hMtop] at hle
    intro x hx
    have hx' : x ∈ Wif := hle trivial
    change x ∈ (Wif : Set K) at hx'
    rw [hWifcoe] at hx'
    exact hx'
  -- ## Step 4: linear disjointness
  set hbasis : Module.Basis (Fin 5) 𝕜 Cyc.L :=
    (Module.finBasis 𝕜 Cyc.L).reindex (finCongr Cyc.finrank_eq)
  set W₂ : Submodule ↥F K := Submodule.span ↥F (Set.range (fun i : Fin 5 => f (hbasis i)))
    with hW₂
  have hsub : (L' : Set K) ⊆ (W₂ : Set K) := by
    intro x hx
    have hx' : x ∈ f.fieldRange := by rw [← hL'def]; exact hx
    obtain ⟨l, rfl⟩ := AlgHom.mem_fieldRange.mp hx'
    show f l ∈ (W₂ : Set K)
    rw [← hbasis.sum_repr l, map_sum]
    refine Submodule.sum_mem W₂ (fun i _ => ?_)
    rw [map_smul]
    have hmem : (⟨algebraMap 𝕜 K (hbasis.repr l i), F.algebraMap_mem _⟩ : ↥F) • f (hbasis i) ∈ W₂ :=
      Submodule.smul_mem W₂ _ (Submodule.subset_span ⟨i, rfl⟩)
    simpa using hmem
  have hspan2 : ⊤ ≤ W₂ := le_trans hWtop (Submodule.span_le.mpr hsub)
  have hli : LinearIndependent ↥F (fun i : Fin 5 => f (hbasis i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan2 (by rw [Fintype.card_fin, hfinF])
  exact ⟨IntermediateField.LinearDisjoint.of_basis_right' (A := F) (b := hbasis) hli, hMtop, hfinF⟩

end Work.MotC
