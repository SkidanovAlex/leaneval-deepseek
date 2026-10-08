import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# Brauer's permutation lemma

A self-contained proof of Brauer's permutation lemma over `ℂ`:

If `M : ι → κ → ℂ` has linearly independent rows (so, with `#ι = #κ`, `M` is an
invertible linear map `(κ → ℂ) →ₗ (ι → ℂ)`), and permutations `σ` of `ι`, `τ` of
`κ` satisfy `M (σ i) j = M i (τ j)`, then `σ` and `τ` have the same number of
fixed points.

The proof shows that the two permutation operators are conjugate (hence have the
same trace), and computes the trace of a permutation operator as the number of
its fixed points.
-/

namespace Work.Clifford

/-- Precomposition by an equivalence, as a linear endomorphism of `α → ℂ`. -/
def permLin {α : Type*} (e : α ≃ α) : (α → ℂ) →ₗ[ℂ] (α → ℂ) where
  toFun v := v ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem permLin_apply {α : Type*} (e : α ≃ α) (v : α → ℂ) (i : α) :
    permLin e v i = v (e i) := rfl

/-- The linear map `v ↦ M *ᵥ v` attached to a matrix `M : ι → κ → ℂ`. -/
def matLin {ι κ : Type*} [Fintype κ] (M : ι → κ → ℂ) : (κ → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun v i := ∑ j, M i j * v j
  map_add' v w := by ext i; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring

@[simp] theorem matLin_apply {ι κ : Type*} [Fintype κ] (M : ι → κ → ℂ) (v : κ → ℂ)
    (i : ι) : matLin M v i = ∑ j, M i j * v j := rfl

/-- A sum of `0`-`1` indicators over a finite type is the cardinality of the
corresponding subtype. -/
theorem sum_ite_one_eq_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ i : α, (if p i then (1:ℂ) else 0)) = (Fintype.card {i // p i} : ℂ) := by
  rw [Fintype.card_subtype]
  rw [Finset.card_filter]
  push_cast
  simp

/-- The trace of a permutation operator is the sum of the root-of-unity-valued
indicators of its fixed points. -/
theorem trace_permLin_eq_sum {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    LinearMap.trace ℂ (α → ℂ) (permLin e) = ∑ i : α, (if e i = i then (1:ℂ) else 0) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ α) (permLin e)]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, permLin_apply,
    Pi.basisFun_apply, Pi.single_apply]

/-- The trace of a permutation operator is the number of its fixed points. -/
theorem trace_permLin_eq_card {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    LinearMap.trace ℂ (α → ℂ) (permLin e) = (Nat.card {i : α // e i = i} : ℂ) := by
  rw [trace_permLin_eq_sum e, sum_ite_one_eq_card (fun i : α => e i = i),
    Nat.card_eq_fintype_card]

theorem brauer_permutation_lemma {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (σ : ι ≃ ι) (τ : κ ≃ κ)
    (hindep : LinearIndependent ℂ M) (hcard : Fintype.card ι = Fintype.card κ)
    (hrel : ∀ i j, M (σ i) j = M i (τ j)) :
    Nat.card {i : ι // σ i = i} = Nat.card {j : κ // τ j = j} := by
  classical
  by_cases hne : Nonempty ι
  · haveI : Nonempty ι := hne
    -- The rows of `M` span `κ → ℂ`, because they are independent and there are
    -- exactly `finrank ℂ (κ → ℂ) = card κ = card ι` of them.
    have hdim : Fintype.card ι = Module.finrank ℂ (κ → ℂ) := by
      rw [Module.finrank_fintype_fun_eq_card]; exact hcard
    have hspan : Submodule.span ℂ (Set.range M) = ⊤ :=
      LinearIndependent.span_eq_top_of_card_eq_finrank hindep hdim
    -- Hence `matLin M` is injective.
    have hker : ∀ v : κ → ℂ, matLin M v = 0 → v = 0 := by
      intro v hv
      have hv0 : ∀ i, ∑ j, M i j * v j = 0 := by
        intro i
        have := congrFun hv i
        simpa using this
      let φ : (κ → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun w => ∑ j, w j * v j
          map_add' := by intro a b; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          map_smul' := by
            intro c w
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring }
      have hφ : ∀ i, φ (M i) = 0 := by intro i; simpa [φ] using hv0 i
      have hle : Submodule.span ℂ (Set.range M) ≤ LinearMap.ker φ := by
        rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        exact LinearMap.mem_ker.mpr (hφ i)
      have htop : LinearMap.ker φ = ⊤ := top_le_iff.mp (hspan ▸ hle)
      funext k
      have hmem : Pi.single k (1:ℂ) ∈ LinearMap.ker φ := by rw [htop]; trivial
      have h1 := LinearMap.mem_ker.mp hmem
      simpa [φ, Pi.single_apply] using h1
    have hinj : Function.Injective (matLin M) := by
      intro u w huw
      have h0 : matLin M (u - w) = 0 := by rw [map_sub, huw, sub_self]
      have := hker (u - w) h0
      rwa [sub_eq_zero] at this
    have hfin : Module.finrank ℂ (κ → ℂ) = Module.finrank ℂ (ι → ℂ) := by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
      exact hcard.symm
    have hsurj : Function.Surjective (matLin M) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := matLin M) hfin).mp hinj
    let e : (κ → ℂ) ≃ₗ[ℂ] (ι → ℂ) := LinearEquiv.ofBijective (matLin M) ⟨hinj, hsurj⟩
    -- The commutation relation `matLin M ∘ S = R ∘ matLin M`.
    have hcommM : matLin M ∘ₗ permLin τ.symm = permLin σ ∘ₗ matLin M := by
      apply LinearMap.ext
      intro w
      apply funext
      intro i
      simp only [LinearMap.comp_apply, matLin_apply, permLin_apply]
      have h1 : (∑ j, M i j * w (τ.symm j)) = (∑ j, M i (τ j) * w j) := by
        rw [← Equiv.sum_comp τ (fun j => M i j * w (τ.symm j))]
        simp
      have h2 : (∑ j, M i (τ j) * w j) = (∑ j, M (σ i) j * w j) := by
        apply Finset.sum_congr rfl; intro j _; rw [hrel]
      rw [h1, h2]
    have hue : (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) = matLin M := rfl
    have hcomm : (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) ∘ₗ permLin τ.symm =
        permLin σ ∘ₗ (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) := by
      rw [hue]; exact hcommM
    have hc1 : (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) ∘ₗ
        (e.symm : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) = LinearMap.id := by
      ext x; simp
    have hc2 : (e.symm : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) ∘ₗ
        (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)) = LinearMap.id := by
      ext x; simp
    -- Similarity of the two permutation operators.
    have htrace : LinearMap.trace ℂ (ι → ℂ) (permLin σ) =
        LinearMap.trace ℂ (κ → ℂ) (permLin τ.symm) := by
      have h := LinearMap.trace_comp_comm' (R := ℂ)
        (f := (e.symm : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)))
        (g := permLin σ ∘ₗ (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ)))
      rw [LinearMap.comp_assoc, hc1, LinearMap.comp_id, ← hcomm, ← LinearMap.comp_assoc,
        hc2, LinearMap.id_comp] at h
      exact h
    have hσ : LinearMap.trace ℂ (ι → ℂ) (permLin σ) = (Nat.card {i : ι // σ i = i} : ℂ) :=
      trace_permLin_eq_card σ
    have hτ : LinearMap.trace ℂ (κ → ℂ) (permLin τ.symm) =
        (Nat.card {j : κ // τ.symm j = j} : ℂ) :=
      trace_permLin_eq_card τ.symm
    have hfix : Nat.card {j : κ // τ.symm j = j} = Nat.card {j : κ // τ j = j} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun j => by rw [Equiv.symm_apply_eq, eq_comm])
    have key : (Nat.card {i : ι // σ i = i} : ℂ) = (Nat.card {j : κ // τ j = j} : ℂ) := by
      rw [← hσ, htrace, hτ, hfix]
    exact Nat.cast_injective key
  · -- Degenerate case: `ι` (and hence `κ`) is empty.
    haveI : IsEmpty ι := not_nonempty_iff.mp hne
    have hcardκ : Fintype.card κ = 0 := by
      rw [← hcard]; exact Fintype.card_eq_zero_iff.mpr ‹IsEmpty ι›
    haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcardκ
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Fintype.card_eq_zero_iff.mpr (show IsEmpty {i : ι // σ i = i} from
          ⟨fun x => isEmptyElim x.1⟩),
        Fintype.card_eq_zero_iff.mpr (show IsEmpty {j : κ // τ j = j} from
          ⟨fun x => isEmptyElim x.1⟩)]

end Work.Clifford
