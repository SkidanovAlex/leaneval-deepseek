import Mathlib
import Submission.Work.SSGRoute.PT.relaxed_converse_of_finiteS_v2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

/-! ## Two linear-algebra lemmas used by the reduction

Every submodule of a vector space over a field is a direct summand, so a linear functional on a
submodule extends to the whole space; and a functional on a finite product of modules is a finite
sum of functionals on the factors. -/

/-- A linear functional on a submodule of a vector space over a field extends to the whole
space. -/
private theorem exists_extend_functional {𝔽 E : Type*} [Field 𝔽] [AddCommGroup E]
    [Module 𝔽 E] (W : Submodule 𝔽 E) (φ : W →ₗ[𝔽] 𝔽) :
    ∃ Φ : E →ₗ[𝔽] 𝔽, ∀ w : W, Φ w = φ w := by
  obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl W
  refine ⟨φ.comp (Submodule.projectionOnto W W' hcompl), fun w => ?_⟩
  show φ (Submodule.projectionOnto W W' hcompl ↑w) = φ w
  rw [Submodule.projectionOnto_apply_left hcompl w]

/-- **Splitting of a linear functional along a finite family of linear maps.**  If `lam` vanishes
on the intersection of the kernels of the maps `ψ i` (`i : ι`, `ι` finite) then it is a finite sum
of functionals on the targets composed with the maps. -/
private theorem exists_sum_of_comp_of_iInf_ker_le {𝔽 : Type*} [Field 𝔽] {V : Type*}
    [AddCommGroup V] [Module 𝔽 V] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module 𝔽 (A i)]
    (ψ : ∀ i, V →ₗ[𝔽] A i) (lam : V →ₗ[𝔽] 𝔽) (h : (⨅ i, (ψ i).ker) ≤ lam.ker) :
    ∃ Λ : ∀ i, A i →ₗ[𝔽] 𝔽, ∀ v : V, (∑ i, Λ i (ψ i v)) = lam v := by
  classical
  let Ψ : V →ₗ[𝔽] ((i : ι) → A i) := LinearMap.pi ψ
  have hker : Ψ.ker ≤ lam.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    refine h ?_
    rw [Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker]
    have h2 : Ψ v i = 0 := by rw [hv]; rfl
    exact h2
  let ℓ₀ : V ⧸ Ψ.ker →ₗ[𝔽] 𝔽 := Ψ.ker.liftQ lam hker
  let ℓ : Ψ.range →ₗ[𝔽] 𝔽 := ℓ₀.comp (LinearMap.quotKerEquivRange Ψ).symm.toLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_extend_functional Ψ.range ℓ
  let Λ : ∀ i, A i →ₗ[𝔽] 𝔽 := (LinearMap.lsum 𝔽 A 𝔽).symm Φ
  refine ⟨Λ, fun v => ?_⟩
  have h1 : (∑ i, Λ i (ψ i v)) = Φ (Ψ v) := by
    have hstep : ∀ i, Λ i (ψ i v) = Φ (Pi.single i (Ψ v i)) := by
      intro i
      have hΛi : Λ i = Φ ∘ₗ LinearMap.single 𝔽 A i :=
        LinearMap.lsum_symm_apply 𝔽 A 𝔽 Φ i
      rw [hΛi, LinearMap.comp_apply, LinearMap.single_apply]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hstep i), ← map_sum, Finset.univ_sum_single]
  rw [h1]
  have h2 : ℓ ⟨Ψ v, ⟨v, rfl⟩⟩ = lam v := by
    have h3 : (LinearMap.quotKerEquivRange Ψ).symm ⟨Ψ v, ⟨v, rfl⟩⟩ =
        Submodule.Quotient.mk v := by
      apply (LinearMap.quotKerEquivRange Ψ).injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk Ψ v)
    show ℓ₀ ((LinearMap.quotKerEquivRange Ψ).symm ⟨Ψ v, ⟨v, rfl⟩⟩) = lam v
    rw [h3]
    exact Submodule.liftQ_apply Ψ.ker lam v
  rw [hΦ ⟨Ψ v, ⟨v, rfl⟩⟩, h2]

/-- **A `Finset`-indexed family of local existence statements gives a single function.** -/
private theorem exists_fun_forall_mem_finset {α β : Type*} (s : Finset α) (d : β)
    (P : α → β → Prop) (h : ∀ t ∈ s, ∃ a : β, P t a) :
    ∃ f : α → β, ∀ t ∈ s, P t (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => d, by intro t ht; exact absurd ht (Finset.notMem_empty t)⟩
  | insert t s ht hIH =>
      have hs : ∀ u ∈ s, ∃ a : β, P u a := fun u hu => h u (Finset.mem_insert_of_mem hu)
      obtain ⟨f, hf⟩ := hIH hs
      obtain ⟨a, ha⟩ := h t (Finset.mem_insert_self t s)
      refine ⟨fun A => if A = t then a else f A, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simp only [if_pos rfl]
        exact ha
      · simp only [if_neg (fun hh : u = t => ht (hh ▸ hu))]
        exact hf u hu

/-- Clause (8) of `G1⁺` (the relaxed converse with escape at `cs(N)`) from the finite-`S` converse,
version 2.

Change from v1, which was declared mis-stated, correctly: the factoring step needs `λ` additive in
`b`, including its involution terms `Σ_{c∈C} pair(β_c, b)`.  `haddArch` adds additivity in the
second variable at the involution groups.  Realisability (`hreal`) is still needed only at the
finite escape places `T'`.

Route.
(1) `exists_finite_escape_detecting` with `X = M'` gives `T'`, split in `N`, outside `S`.  Put
`S₁ = S ∪ T'`.
(2) `λ(b) := Σ_S pair(α_A, b) + Σ_C pair(β_c, b)`, defined on global `M'`-cocycles vanishing on
inertia outside `S₁`.  It is additive (`hadd`, `haddArch`).  If such a `b` is a coboundary at
every `t ∈ T'`, then step (1) makes it a relaxed dual Selmer cocycle: inertia vanishing at the
non-split places outside `S` holds because `T'` is split.  So `λ(b) = 0` by the hypothesis.
(3) Linear algebra over `𝔽_p`: `λ` factors through `b ↦ ([b|_{D_t}])_{t ∈ T'}`.  Extend from the
image to `⊕_t H¹(D_t, M')` and split into `Σ_t λ_t`; `hreal` gives `α_t` with
`pair(α_t, ·) = -λ_t`.
(4) `hfinS` at `S₁` with `α` extended by `α_t`.  `S₁` covers the places over `p` and those ramified
in `K`, since `S` covers those ramified in `N ⊇ K`.  The resulting `ε` is unramified outside
`S ∪ T' ⊆ S ∪ cs(N)`. -/
theorem relaxed_converse_of_finiteS_v3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hadd : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
        pair M (SSGRoute.decomp k A) a (b + b') =
          pair M (SSGRoute.decomp k A) a b + pair M (SSGRoute.decomp k A) a b')
    (haddArch : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (c : (Ω ≃ₐ[k] Ω)), c ^ 2 = 1 →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        pair M (Subgroup.zpowers c) a (b + b') =
          pair M (Subgroup.zpowers c) a b + pair M (Subgroup.zpowers c) a b')
    (hreal : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
        (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          lam (b + b') = lam b + lam b') →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
        ∃ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
          ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            pair M (SSGRoute.decomp k A) a b = lam b)
    (hfinS : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (S₁ : Finset (ValuationSubring Ω)), (∀ A ∈ S₁, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B) →
      ∀ (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
      (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
      (∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A)) →
      (∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
          ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
        ∑ A ∈ S₁, pair M (SSGRoute.decomp k A) (α A) b +
          ∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b = 0) →
      ∃ ε : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
        (∀ A ∈ S₁, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
          (fun σ => ε σ - α A σ)) ∧
        (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
          (fun σ => ε σ - β c σ)) ∧
        ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
          ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → ε σ = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b +
        ∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b = 0) :
    ∃ ε : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
      (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  -- the dual coefficient module `M^∨(1) = DualMod p (M ⊗ T)` and its finiteness
  let X := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)
  have hXfin : Finite X := by
    have h1 : Finite (TensorProduct (ZMod p) M T) := by
      have hM : Module.Finite (ZMod p) M := Module.Finite.of_finite
      have hT : Module.Finite (ZMod p) T :=
        Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
      have h2 : Module.Finite (ZMod p) (TensorProduct (ZMod p) M T) := inferInstance
      exact Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun f : X => (f : TensorProduct (ZMod p) M T → ZMod p))
      (fun a b h => LinearMap.ext (fun x => congrFun h x))
  letI : AddCommGroup X :=
    inferInstanceAs (AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  letI : Module (ZMod p) X :=
    inferInstanceAs (Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  letI : DistribMulAction (K ≃ₐ[k] K) X := inferInstanceAs
    (DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) X := inferInstanceAs
    (SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  letI : Finite X := hXfin
  -- (1) finitely many split places detect the relaxed condition
  obtain ⟨T', hT'1, hT'2, hT'3⟩ :=
    Work.SSGRoute.PT.exists_finite_escape_detecting p k Ω K N hKN S hSfin hSram X
  -- the whole extension `N/k` is normal, and `K ≤ N`, so `D_B ≤ G_K` for split `B`
  have hNormN : (N.fixingSubgroup).Normal := IsGalois.fixingSubgroup_normal_of_isGalois N
  have hsplit_le : ∀ B : ValuationSubring Ω, SSGRoute.IsSplitIn k N B →
      SSGRoute.decomp k B ≤ K.fixingSubgroup :=
    fun B hB => le_trans hB (IntermediateField.fixingSubgroup_le hKN)
  -- (2) the enlarged place set
  let S₁ : Finset (ValuationSubring Ω) := S ∪ T'
  have hST'disj : Disjoint S T' := by
    rw [Finset.disjoint_left]
    intro A hA hAT'
    exact (hT'1 A hAT').2.2 A hA (Work.SSGRoute.isConjPlace_refl A)
  have hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hSfin A h
    · exact (hT'1 A h).1
  have hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B := by
    intro A hA B hB hc
    rcases Finset.mem_union.mp hA with hA | hA
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact hSdisj A hA B hB hc
      · exact absurd hc ((hT'1 B hB).2.2 A hA)
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact absurd (Work.SSGRoute.isConjPlace_symm hc) ((hT'1 A hA).2.2 B hB)
      · exact hT'2 A hA B hB hc
  have hramKN : ∀ B : ValuationSubring Ω, SSGRoute.IsRamifiedIn k K B →
      SSGRoute.IsRamifiedIn k N B := by
    rintro B ⟨σ, hσI, hσK⟩
    exact ⟨σ, hσI, fun hσN => hσK (IntermediateField.fixingSubgroup_le hKN hσN)⟩
  have hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B := by
    intro B hB h
    obtain ⟨A, hA, hc⟩ := hSram B hB (h.elim (fun h1 => Or.inl (hramKN B h1)) Or.inr)
    exact ⟨A, Finset.mem_union_left T' hA, hc⟩
  -- (3) the space of global `M'`-cocycles unramified outside `S₁`
  let V : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → X) := Work.SSGRoute.PTCore.Z1unr p k Ω K X S₁
  have hVmem : ∀ b : (Ω ≃ₐ[k] Ω) → X, b ∈ V ↔
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0 :=
    fun b => Work.SSGRoute.PTCore.mem_Z1unr
  -- the functional `λ` of the route
  let pairS : ((Ω ≃ₐ[k] Ω) → X) → ZMod p := fun b =>
    (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b) +
    (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b)
  have hpairS_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → X, b ∈ V → b' ∈ V →
      pairS (b + b') = pairS b + pairS b' := by
    intro b b' hb hb'
    have hcoc : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
      fun A _ => Work.SSGRoute.isCocycleOn_mono _ le_top ((hVmem b).mp hb).1
    have hcoc' : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' :=
      fun A _ => Work.SSGRoute.isCocycleOn_mono _ le_top ((hVmem b').mp hb').1
    have hScoc : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
      fun c _ => Work.SSGRoute.isCocycleOn_mono _ le_top ((hVmem b).mp hb).1
    have hScoc' : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' :=
      fun c _ => Work.SSGRoute.isCocycleOn_mono _ le_top ((hVmem b').mp hb').1
    have hS : (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) (b + b')) =
        (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b) +
        (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b') := by
      have h1 : (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) (b + b')) =
          ∑ A ∈ S, (pair M (SSGRoute.decomp k A) (α A) b +
            pair M (SSGRoute.decomp k A) (α A) b') :=
        Finset.sum_congr rfl (fun A hA => hadd M A (hSfin A hA) (α A)
          b b' (hα A hA).1 (hα A hA).2
          (hcoc A hA) (Work.SSGRoute.isLocConstOn_mono le_top ((hVmem b).mp hb).2.1)
          (hcoc' A hA) (Work.SSGRoute.isLocConstOn_mono le_top ((hVmem b').mp hb').2.1))
      rw [h1, Finset.sum_add_distrib]
    have hC : (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) (b + b')) =
        (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b) +
        (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b') := by
      have h1 : (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) (b + b')) =
          ∑ c ∈ C, (pair M (Subgroup.zpowers c) (β c) b +
            pair M (Subgroup.zpowers c) (β c) b') :=
        Finset.sum_congr rfl (fun c hc => haddArch M c (hCinv c hc) (β c)
          b b' (hScoc c hc) (hScoc' c hc))
      rw [h1, Finset.sum_add_distrib]
    simp only [pairS]
    rw [hS, hC]
    abel
  have hpairS_zero : pairS 0 = 0 := by
    have hS : (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) (0 : (Ω ≃ₐ[k] Ω) → X)) = 0 := by
      refine Finset.sum_eq_zero (fun A hA => ?_)
      have h := hadd M A (hSfin A hA) (α A)
        (0 : (Ω ≃ₐ[k] Ω) → X) 0 (hα A hA).1 (hα A hA).2
        Work.SSGRoute.isCocycleOn_zero Work.SSGRoute.isLocConstOn_zero
        Work.SSGRoute.isCocycleOn_zero Work.SSGRoute.isLocConstOn_zero
      rw [add_zero] at h
      exact add_left_cancel (show pair M (SSGRoute.decomp k A) (α A) 0 +
          pair M (SSGRoute.decomp k A) (α A) 0 =
          pair M (SSGRoute.decomp k A) (α A) 0 + 0 by rw [add_zero]; exact h.symm)
    have hC : (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) (0 : (Ω ≃ₐ[k] Ω) → X)) = 0 := by
      refine Finset.sum_eq_zero (fun c hc => ?_)
      have h := haddArch M c (hCinv c hc) (β c)
        (0 : (Ω ≃ₐ[k] Ω) → X) 0 Work.SSGRoute.isCocycleOn_zero Work.SSGRoute.isCocycleOn_zero
      rw [add_zero] at h
      exact add_left_cancel (show pair M (Subgroup.zpowers c) (β c) 0 +
          pair M (Subgroup.zpowers c) (β c) 0 =
          pair M (Subgroup.zpowers c) (β c) 0 + 0 by rw [add_zero]; exact h.symm)
    simp only [pairS, hS, hC, add_zero]
  let lam : ↥V →ₗ[ZMod p] ZMod p := AddMonoidHom.toZModLinearMap p
    { toFun := fun b => pairS (b : (Ω ≃ₐ[k] Ω) → X)
      map_zero' := hpairS_zero
      map_add' := fun b b' => by
        show pairS ((b + b' : ↥V) : (Ω ≃ₐ[k] Ω) → X) = pairS (b : _) + pairS (b' : _)
        rw [Submodule.coe_add]
        exact hpairS_add b.1 b'.1 b.2 b'.2 }
  -- the subspace on which `λ` vanishes: coboundary at every escape place
  let W : Submodule (ZMod p) ↥V :=
    { carrier := {b : ↥V | ∀ t ∈ T',
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k t)
          (b : (Ω ≃ₐ[k] Ω) → X)}
      zero_mem' := fun t _ => Work.SSGRoute.isCoboundaryOn_zero
      add_mem' := by
        intro b b' hb hb' t ht
        rw [Submodule.coe_add]
        exact Work.SSGRoute.isCoboundaryOn_add (hb t ht) (hb' t ht)
      smul_mem' := by
        intro a b hb t ht
        rw [Submodule.coe_smul]
        exact Work.SSGRoute.isCoboundaryOn_smul (hb t ht) a }
  have hlamW : ∀ b : ↥V, b ∈ W → lam b = 0 := by
    intro b hb
    have hbV : (b : (Ω ≃ₐ[k] Ω) → X) ∈ V := b.2
    have hb1 := ((hVmem b).mp hbV).1
    have hb2 := ((hVmem b).mp hbV).2.1
    have hb3 := ((hVmem b).mp hbV).2.2
    -- `b` satisfies the hypotheses of `horth`: it is unramified outside `S₁`
    have hunrT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∀ t ∈ T', ¬ SSGRoute.IsConjPlace k t B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b.1 σ = 0 := by
      intro B hB hBS hBT σ hσ
      exact hb3 B hB (fun A hA => by
        rcases Finset.mem_union.mp hA with h | h
        · exact hBS A h
        · exact hBT A h) σ hσ
    have hcobSplit : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b.1 :=
      fun B hB hBS hBsplit => hT'3 b.1 hb1 hb2 hunrT (fun t ht => hb t ht) B hB hBS hBsplit
    have hvan : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b.1 σ = 0 := by
      intro B hB hBS hBns σ hσ
      exact hb3 B hB (fun A hA => by
        rcases Finset.mem_union.mp hA with h | h
        · exact hBS A h
        · intro hconj
          obtain ⟨γ, hγ⟩ := hconj
          exact hBns (by
            rw [← hγ]
            exact (Work.SSGRoute.isSplitIn_conj N hNormN A γ).mpr (hT'1 A h).2.1)) σ hσ
    have hsum := horth b.1 hb1 hb2 hcobSplit hvan
    show pairS (b : (Ω ≃ₐ[k] Ω) → X) = 0
    simpa only [pairS] using hsum
  -- (4) `λ` vanishes on the cochains that are zero on every escape decomposition group, so it
  -- factors through the local components at the escape places
  let ψ : ∀ j : ↥T', ↥V →ₗ[ZMod p] (SSGRoute.decomp k j.1 → X) := fun j =>
    { toFun := fun b g => (b : (Ω ≃ₐ[k] Ω) → X) g
      map_add' := fun b b' => rfl
      map_smul' := fun a b => rfl }
  have hsplitHyp : (⨅ j : ↥T', (ψ j).ker) ≤ lam.ker := by
    intro v hv
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_iInf] at hv
    refine hlamW v ?_
    intro t ht
    have hmem : (ψ ⟨t, ht⟩) v = 0 := by
      have h2 : v ∈ (ψ ⟨t, ht⟩).ker := hv ⟨t, ht⟩
      rwa [LinearMap.mem_ker] at h2
    exact (Work.SSGRoute.PT.isCoboundaryOn_decomp_iff_forall_eq_zero (K := K)
      (v : (Ω ≃ₐ[k] Ω) → X) (hsplit_le t (hT'1 t ht).2.1)).mpr (fun g hg => by
        have h3 := congrFun hmem ⟨g, hg⟩
        simpa [ψ] using h3)
  obtain ⟨Λ, hΛ⟩ := exists_sum_of_comp_of_iInf_ker_le ψ lam hsplitHyp
  -- the same functionals, indexed by places
  let Λ' : ∀ A : ValuationSubring Ω, (SSGRoute.decomp k A → X) →ₗ[ZMod p] ZMod p :=
    fun A => if h : A ∈ T' then Λ ⟨A, h⟩ else 0
  let lamE : (A : ValuationSubring Ω) → (((Ω ≃ₐ[k] Ω) → X) → ZMod p) :=
    fun A b => - (Λ' A (fun g : SSGRoute.decomp k A => b g))
  have hlamE_eq : ∀ (A : ValuationSubring Ω) (hA : A ∈ T'),
      lamE A = fun b => - (Λ ⟨A, hA⟩ (fun g : SSGRoute.decomp k A => b g)) := by
    intro A hA
    funext b
    simp only [lamE, Λ', dif_pos hA]
  have hsumlamE : ∀ b : ↥V, (∑ t ∈ T', lamE t (b : (Ω ≃ₐ[k] Ω) → X)) = - lam b := by
    intro b
    have h1 : (∑ t ∈ T', lamE t (b : (Ω ≃ₐ[k] Ω) → X)) =
        - (∑ t ∈ T', Λ' t (fun g : SSGRoute.decomp k t => (b : (Ω ≃ₐ[k] Ω) → X) g)) := by
      simp only [lamE, Finset.sum_neg_distrib]
    have h2 : (∑ t ∈ T', Λ' t (fun g : SSGRoute.decomp k t => (b : (Ω ≃ₐ[k] Ω) → X) g)) =
        ∑ j : ↥T', Λ j (ψ j b) := by
      rw [← Finset.sum_attach T'
        (fun t => Λ' t (fun g : SSGRoute.decomp k t => (b : (Ω ≃ₐ[k] Ω) → X) g))]
      rw [Finset.univ_eq_attach]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hΛj : Λ' j.1 = Λ j := by
        simp only [Λ', dif_pos j.2]
      rw [hΛj]
      rfl
    rw [h1, h2, hΛ b]
  -- (5) local realisability at the escape places (`hreal`)
  have hrealE : ∀ t ∈ T', ∃ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) a ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k t) a ∧
      ∀ b : (Ω ≃ₐ[k] Ω) → X,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k t) b →
        pair M (SSGRoute.decomp k t) a b = lamE t b := by
    intro t ht
    obtain ⟨hfin, hsplit, -⟩ := hT'1 t ht
    refine hreal M t hfin (lamE t) ?_ ?_
    · intro b b' hb hb'
      rw [hlamE_eq t ht]
      have hrest : (fun g : SSGRoute.decomp k t => (b + b') g) =
          (fun g : SSGRoute.decomp k t => b g) + (fun g : SSGRoute.decomp k t => b' g) := rfl
      show -(Λ ⟨t, ht⟩ (fun g : SSGRoute.decomp k t => (b + b') g)) =
        -(Λ ⟨t, ht⟩ (fun g : SSGRoute.decomp k t => b g)) +
        -(Λ ⟨t, ht⟩ (fun g : SSGRoute.decomp k t => b' g))
      rw [hrest, map_add]
      abel
    · intro b hb
      rw [hlamE_eq t ht]
      have h0 : (fun g : SSGRoute.decomp k t => b g) = 0 := by
        funext g
        exact (Work.SSGRoute.PT.isCoboundaryOn_decomp_iff_forall_eq_zero (K := K) b
          (hsplit_le t hsplit)).mp hb g g.2
      show -(Λ ⟨t, ht⟩ (fun g : SSGRoute.decomp k t => b g)) = 0
      rw [h0, map_zero, neg_zero]
  -- package the local realisers into a single function of the place
  have hexa : ∃ aesc : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M,
      ∀ t : ValuationSubring Ω, t ∈ T' →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) (aesc t) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k t) (aesc t) ∧
        ∀ b : (Ω ≃ₐ[k] Ω) → X,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k t) b →
          pair M (SSGRoute.decomp k t) (aesc t) b = lamE t b :=
    exists_fun_forall_mem_finset T' (0 : (Ω ≃ₐ[k] Ω) → M)
      (fun t a => SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k t) a ∧
        ∀ b : (Ω ≃ₐ[k] Ω) → X,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k t) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k t) b →
          pair M (SSGRoute.decomp k t) a b = lamE t b) hrealE
  obtain ⟨aesc, haesc⟩ := hexa
  -- (6) extend `α` by the local realisers at the escape places and apply `hfinS`
  have hT'notS : ∀ t ∈ T', t ∉ S := fun t ht hS =>
    (hT'1 t ht).2.2 t hS (Work.SSGRoute.isConjPlace_refl t)
  let α' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M := fun A => if A ∈ S then α A else aesc A
  have hα'S : ∀ A ∈ S, α' A = α A := by
    intro A hA
    simp only [α']
    exact if_pos hA
  have hα'T' : ∀ t ∈ T', α' t = aesc t := by
    intro t ht
    simp only [α']
    exact if_neg (hT'notS t ht)
  have hα'S₁ : ∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α' A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α' A) := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · rw [hα'S A hA]; exact hα A hA
    · rw [hα'T' A hA]; exact ⟨(haesc A hA).1, (haesc A hA).2.1⟩
  have horthS₁ : ∀ b : (Ω ≃ₐ[k] Ω) → X,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
      (∑ A ∈ S₁, pair M (SSGRoute.decomp k A) (α' A) b) +
        (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b) = 0 := by
    intro b hbc hblc hunr
    have hbV : b ∈ V := (hVmem b).mpr ⟨hbc, hblc, hunr⟩
    have hSsum : (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α' A) b) =
        ∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b :=
      Finset.sum_congr rfl (fun A hA => by rw [hα'S A hA])
    have hTsum : (∑ t ∈ T', pair M (SSGRoute.decomp k t) (α' t) b) =
        ∑ t ∈ T', lamE t b := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [hα'T' t ht]
      exact (haesc t ht).2.2 b (Work.SSGRoute.isCocycleOn_mono _ le_top hbc)
        (Work.SSGRoute.isLocConstOn_mono le_top hblc)
    have hunion : (∑ A ∈ S₁, pair M (SSGRoute.decomp k A) (α' A) b) =
        (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b) +
        (∑ t ∈ T', lamE t b) := by
      rw [show S₁ = S ∪ T' from rfl, Finset.sum_union hST'disj, hSsum, hTsum]
    have hdef : lam ⟨b, hbV⟩ = (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b) +
        (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b) := by
      show pairS b = (∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b) +
        (∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b)
      simp only [pairS]
    rw [hunion, hsumlamE ⟨b, hbV⟩, hdef]
    abel
  obtain ⟨ε, hε1, hε2, hε3, hε4, hε5⟩ :=
    hfinS M S₁ hS₁fin hS₁disj hS₁ram C hCinv hC hCdisj α' β hα'S₁ hβ horthS₁
  refine ⟨ε, hε1, hε2, ?_, ?_, ?_⟩
  · intro A hA
    have h := hε3 A (Finset.mem_union_left T' hA)
    rwa [hα'S A hA] at h
  · exact hε4
  · intro B hBfin hBS hBns σ hσ
    refine hε5 B hBfin (fun A hA => ?_) σ hσ
    rcases Finset.mem_union.mp hA with h | h
    · exact hBS A h
    · intro hconj
      obtain ⟨γ, hγ⟩ := hconj
      exact hBns (by
        rw [← hγ]
        exact (Work.SSGRoute.isSplitIn_conj N hNormN A γ).mpr (hT'1 A h).2.1)

end Work.SSGRoute.PT
