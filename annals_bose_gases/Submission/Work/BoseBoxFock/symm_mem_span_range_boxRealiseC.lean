import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.complexRealise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.symm_mem_span_range_boxRealiseC`

A **symmetric** function `f : (Fin d → ℝ³) → ℂ` that lies in the `ℂ`-span of the *labelling
monomials*

    T_l(x) = ∏ i, e (l i) (x i)         (l : Fin d → Fin m)

is `boxRealiseC e d` of some complexified Fock vector `Ψ : CFock m = (Fin m →₀ ℕ) →₀ ℂ`.

## The mathematics

Write `α_l := modeMult l` for the occupation multi-index of the labelling `l`.  The two relevant
facts are

* `boxRealiseC e d Ψ = ∑_α (Ψ α) • (α!/√(d!)) • M_α`, where `M_α = modeProd e d α` is the
  **symmetric mode product** `M_α = Σ_{modeMult σ = α} T_σ`.  Hence the image of `boxRealiseC e d`
  is exactly `span_ℂ{M_α : α.sum = d}`.  In particular every `M_α` is **symmetric** in the
  coordinates, so `range (boxRealiseC e d) ⊆ span_ℂ{T_l} ∩ Sym`.

* Conversely, if `f = Σ_l c_l T_l` is symmetric, average over the coordinate permutations:
  `f = (1/d!) Σ_σ ρ_σ f` with `ρ_σ f = f ∘ (· ∘ σ)`.  Since `ρ_σ T_l = T_{l ∘ σ⁻¹}`, a change of
  variable in the (finite) labelling sum turns this into `f = Σ_l b_l T_l` with the *symmetrised*
  coefficients `b_l = (1/d!) Σ_σ c_{l ∘ σ}`.  These satisfy `b_{l ∘ τ} = b_l`, and two labellings
  have the same occupation multi-index iff they differ by a permutation of the labels
  (`exists_perm_of_modeMult_eq`, proved here from the fibre-cardinality reading of `modeMult`).
  Hence `b` is constant on the fibres of `modeMult` and `Σ_l b_l T_l = Σ_α b_α M_α`.

So `span_ℂ{T_l} ∩ Sym = span_ℂ{M_α}` and `f` is realised — no orthogonality of the modes is used,
and no integral: the identity is purely algebraic.

## Contents

* `tensorMode`, `permActLM`, `permActLM_prod`, `compEquiv`, `sum_comp_perm`;
* `modeMult_apply'`, `modeMult_sum'`, `exists_perm_of_modeMult_eq`;
* `avgCoeff`, `avgCoeff_comp`, `avgCoeff_eq_of_modeMult_eq`;
* `modeMultImage`, `symmCoeff`, `symmCoeff_modeMult`, `sum_avgCoeff_tensorMode`;
* the target `symm_mem_span_range_boxRealiseC`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The labelling monomials and the coordinate action -/

/-- **The `d`-fold product of the modes along a labelling** `l : Fin d → Fin m`:
`T_l(x) = ∏ i, e (l i) (x i)`.  These are the generators appearing in the hypothesis `hf` of
`symm_mem_span_range_boxRealiseC`. -/
def tensorMode {m d : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ) (l : Fin d → Fin m) :
    (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ :=
  fun x => ∏ i, e (l i) (x i)

/-- The action of the coordinate permutation `σ` on configuration functions:
`(σ · f)(x) = f (x ∘ σ)`. -/
def permActLM {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    ((Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) →ₗ[ℂ]
      ((Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) where
  toFun f := fun x => f (x ∘ σ)
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

/-- **The action on the monomials**: `ρ_σ T_l = T_{l ∘ σ⁻¹}` (the labelling is permuted by
`σ⁻¹`, because `σ` acts on the *variables*). -/
lemma permActLM_prod {m d : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (σ : Equiv.Perm (Fin d)) (l : Fin d → Fin m) :
    permActLM σ (fun x => ∏ i, e (l i) (x i)) = fun x => ∏ i, e ((l ∘ σ.symm) i) (x i) := by
  funext x
  simp only [permActLM, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Equiv.prod_comp σ (fun j => e ((l ∘ σ.symm) j) (x j))]
  simp

/-- Reindexing of labellings by a coordinate permutation: `l ↦ l ∘ τ`. -/
def compEquiv {m d : ℕ} (τ : Equiv.Perm (Fin d)) : (Fin d → Fin m) ≃ (Fin d → Fin m) where
  toFun l := l ∘ τ
  invFun l := l ∘ τ.symm
  left_inv l := by ext i; simp
  right_inv l := by ext i; simp

/-- Change of variable `l ↦ l ∘ σ` in a (finite) sum over labellings. -/
lemma sum_comp_perm {m d : ℕ} (σ : Equiv.Perm (Fin d)) {M : Type*} [AddCommMonoid M]
    (G : (Fin d → Fin m) → M) : (∑ l : Fin d → Fin m, G (l ∘ σ)) = ∑ l, G l :=
  Equiv.sum_comp (compEquiv σ) G

/-! ## 2. Occupation multi-indices -/

/-- The components of the occupation multi-index are the fibre cardinalities. -/
lemma modeMult_apply' {m n : ℕ} (σ : Fin n → Fin m) (k : Fin m) :
    Work.BoseDict.modeMult σ k = (Finset.univ.filter fun i => σ i = k).card := by
  rw [Work.BoseDict.modeMult, Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **The total occupation of a labelling is the number of labels.** -/
lemma modeMult_sum' {m n : ℕ} (σ : Fin n → Fin m) :
    (Work.BoseDict.modeMult σ).sum (fun _ k => k) = n := by
  have h : (Work.BoseDict.modeMult σ).degree = n := by
    simp only [Work.BoseDict.modeMult, map_sum, Finsupp.degree_single]
    rw [← Finset.card_eq_sum_card_fiberwise (f := σ) (s := Finset.univ) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)]
    simp
  exact h

/-- **Two labellings with the same occupation multi-index differ by a permutation of the
labels.**  The proof matches the fibres of `l` and `l'` (which have equal cardinality, by the
fibre-cardinality reading of `modeMult`) through `Fintype.equivOfCardEq` and assembles them with
`Equiv.sigmaFiberEquiv`. -/
lemma exists_perm_of_modeMult_eq {m d : ℕ} {l l' : Fin d → Fin m}
    (h : Work.BoseDict.modeMult l = Work.BoseDict.modeMult l') :
    ∃ υ : Equiv.Perm (Fin d), l' = l ∘ υ := by
  classical
  have hcard : ∀ i : Fin m,
      Fintype.card {j : Fin d // l j = i} = Fintype.card {j : Fin d // l' j = i} := by
    intro i
    have h2 : Work.BoseDict.modeMult l i = Work.BoseDict.modeMult l' i :=
      DFunLike.congr_fun h i
    have h1 : (Finset.univ.filter fun j => l j = i).card
        = (Finset.univ.filter fun j => l' j = i).card := by
      rw [← modeMult_apply' l i, ← modeMult_apply' l' i, h2]
    rw [Fintype.card_subtype, Fintype.card_subtype, h1]
  let e : (i : Fin m) → {j : Fin d // l j = i} ≃ {j : Fin d // l' j = i} :=
    fun i => Fintype.equivOfCardEq (hcard i)
  refine ⟨(Equiv.sigmaFiberEquiv l').symm.trans
    ((Equiv.sigmaCongrRight e).symm.trans (Equiv.sigmaFiberEquiv l)), ?_⟩
  have hsymm : ∀ j : Fin d,
      (Equiv.sigmaFiberEquiv l').symm j = ⟨l' j, ⟨j, rfl⟩⟩ := fun j => rfl
  funext j
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply, hsymm, Function.comp_apply]
  exact (((e (l' j)).symm ⟨j, rfl⟩).2).symm

/-! ## 3. Symmetrisation of the labelling coefficients -/

/-- The **symmetrised labelling coefficient**: `b_l = Σ_{σ ∈ Sym(d)} c_{l ∘ σ}` (the `1/d!` is
kept outside, in `symmCoeff`). -/
def avgCoeff {m d : ℕ} (c : (Fin d → Fin m) → ℂ) (l : Fin d → Fin m) : ℂ :=
  ∑ σ : Equiv.Perm (Fin d), c (l ∘ σ)

/-- The symmetrised coefficient is invariant under the right action of `Sym(d)` on the labels. -/
lemma avgCoeff_comp {m d : ℕ} (c : (Fin d → Fin m) → ℂ) (τ : Equiv.Perm (Fin d))
    (l : Fin d → Fin m) : avgCoeff c (l ∘ τ) = avgCoeff c l := by
  have h1 : ∀ σ : Equiv.Perm (Fin d), ((l ∘ τ) ∘ σ) = (l ∘ (τ * σ)) := fun σ => by
    ext i; simp
  simp only [avgCoeff]
  refine (Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => by rw [h1 σ])).trans ?_
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin d) => c (l ∘ σ))

/-- Hence it is constant on the fibres of the occupation map. -/
lemma avgCoeff_eq_of_modeMult_eq {m d : ℕ} {c : (Fin d → Fin m) → ℂ} {l l' : Fin d → Fin m}
    (h : Work.BoseDict.modeMult l = Work.BoseDict.modeMult l') : avgCoeff c l = avgCoeff c l' := by
  obtain ⟨υ, hυ⟩ := exists_perm_of_modeMult_eq h
  rw [hυ, avgCoeff_comp]

/-- The image of the occupation map `l ↦ modeMult l`, as a finite set of multi-indices. -/
noncomputable def modeMultImage (m d : ℕ) : Finset (Fin m →₀ ℕ) :=
  Finset.univ.image (fun l : Fin d → Fin m => Work.BoseDict.modeMult l)

/-- The **symmetric coefficients**, indexed by multi-indices: on the fibre of `α` the value is
`b_l / d!`, and the value is `0` off the image of the occupation map (where it is never used). -/
noncomputable def symmCoeff {m d : ℕ} (c : (Fin d → Fin m) → ℂ) (α : Fin m →₀ ℕ) : ℂ :=
  if h : ∃ l : Fin d → Fin m, Work.BoseDict.modeMult l = α then
    avgCoeff c (Classical.choose h) / (d.factorial : ℂ)
  else 0

/-- `symmCoeff` evaluated at the occupation of a labelling. -/
lemma symmCoeff_modeMult {m d : ℕ} (c : (Fin d → Fin m) → ℂ) (l : Fin d → Fin m) :
    symmCoeff c (Work.BoseDict.modeMult l) = avgCoeff c l / (d.factorial : ℂ) := by
  have h0 : ∃ l' : Fin d → Fin m, Work.BoseDict.modeMult l' = Work.BoseDict.modeMult l :=
    ⟨l, rfl⟩
  rw [symmCoeff, dif_pos h0]
  congr 1
  exact avgCoeff_eq_of_modeMult_eq (Classical.choose_spec h0)

/-! ## 4. The regrouping `Σ_l b_l T_l = Σ_α b_α M_α` -/

/-- **The regrouping.**  A sum over labellings weighted by a coefficient that is constant on the
fibres of the occupation map is a sum over multi-indices of the symmetric mode products. -/
lemma sum_avgCoeff_tensorMode {m d : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (c : (Fin d → Fin m) → ℂ) :
    (∑ l : Fin d → Fin m, (avgCoeff c l / (d.factorial : ℂ)) • tensorMode e l)
      = ∑ α ∈ modeMultImage m d, symmCoeff c α • Work.BoseDict.modeProd e d α := by
  classical
  have hM : ∀ α : Fin m →₀ ℕ,
      (∑ l ∈ Finset.univ.filter (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α),
        tensorMode e l) = Work.BoseDict.modeProd e d α := by
    intro α
    funext x
    rw [Finset.sum_apply, Work.BoseDict.modeProd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : Work.BoseDict.modeMult l = α
    · rw [if_pos h, if_pos h, one_mul]
      rfl
    · rw [if_neg h, if_neg h, zero_mul]
  have hinner : ∀ α ∈ modeMultImage m d,
      (∑ l ∈ Finset.univ.filter (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α),
        symmCoeff c (Work.BoseDict.modeMult l) • tensorMode e l)
        = symmCoeff c α • Work.BoseDict.modeProd e d α := by
    intro α _
    rw [← hM α, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_filter] at hl
    rw [hl.2]
  have hdisj : (↑(modeMultImage m d) : Set (Fin m →₀ ℕ)).PairwiseDisjoint
      (fun α => Finset.univ.filter (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α)) := by
    intro α _ β _ hne
    show Disjoint (Finset.univ.filter fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α)
      (Finset.univ.filter fun l : Fin d → Fin m => Work.BoseDict.modeMult l = β)
    rw [Finset.disjoint_left]
    intro l hl hl'
    rw [Finset.mem_filter] at hl hl'
    exact hne (hl.2.symm.trans hl'.2)
  have hcover : (modeMultImage m d).biUnion
      (fun α => Finset.univ.filter (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α))
      = Finset.univ := by
    refine Finset.Subset.antisymm (fun l _ => Finset.mem_univ l) (fun l _ => ?_)
    exact Finset.mem_biUnion.mpr ⟨Work.BoseDict.modeMult l,
      Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, rfl⟩⟩
  calc (∑ l : Fin d → Fin m, (avgCoeff c l / (d.factorial : ℂ)) • tensorMode e l)
      = ∑ l : Fin d → Fin m, symmCoeff c (Work.BoseDict.modeMult l) • tensorMode e l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [symmCoeff_modeMult]
    _ = ∑ l ∈ (modeMultImage m d).biUnion (fun α => Finset.univ.filter
            (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α)),
          symmCoeff c (Work.BoseDict.modeMult l) • tensorMode e l := by rw [hcover]
    _ = ∑ α ∈ modeMultImage m d, ∑ l ∈ Finset.univ.filter
            (fun l : Fin d → Fin m => Work.BoseDict.modeMult l = α),
          symmCoeff c (Work.BoseDict.modeMult l) • tensorMode e l :=
          Finset.sum_biUnion hdisj
    _ = ∑ α ∈ modeMultImage m d, symmCoeff c α • Work.BoseDict.modeProd e d α :=
          Finset.sum_congr rfl hinner

/-! ## 5. The target -/

/-- **A symmetric function in the span of the labelling monomials is in the image of
`boxRealiseC`.**  This is the `Sym^{|S|}(V_ℂ) = span_ℂ{M_α}` step of the BF3c sector-slice
selection. -/
theorem symm_mem_span_range_boxRealiseC {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    {f : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hfsym : ∀ σ : Equiv.Perm (Fin d),
      (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => f (x ∘ σ)) = f)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun l : Fin d → Fin m =>
        fun x : Fin d → EuclideanSpace ℝ (Fin 3) => ∏ i, e (l i) (x i)))) :
    ∃ Ψ : Work.BoseBoxFock.CFock m, Work.BoseBoxFock.boxRealiseC e d Ψ = f := by
  classical
  -- the coefficients of `f` in the labelling monomials
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have hdf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  -- **(A)** averaging over the coordinate permutations: `f = (1/d!) Σ_σ ρ_σ f`, because `f` is
  -- symmetric.
  have hA : f = (1 / (d.factorial : ℂ)) • (∑ σ : Equiv.Perm (Fin d), permActLM σ f) := by
    have h1 : (∑ σ : Equiv.Perm (Fin d), permActLM σ f) = ∑ _σ : Equiv.Perm (Fin d), f :=
      Finset.sum_congr rfl fun σ _ => hfsym σ
    have h2 : (∑ _σ : Equiv.Perm (Fin d), f) = (d.factorial : ℂ) • f := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℂ d.factorial f).symm
    rw [h1, h2, smul_smul, one_div, inv_mul_cancel₀ hdf, one_smul]
  -- **(B)** expanding the average in the labelling monomials, and changing variables
  -- (`ρ_σ T_l = T_{l ∘ σ⁻¹}`) in the finite sum over labellings.
  have hB : (∑ σ : Equiv.Perm (Fin d), permActLM σ f)
      = ∑ l : Fin d → Fin m, avgCoeff c l • tensorMode e l := by
    have hsub : ∀ σ : Equiv.Perm (Fin d),
        permActLM σ f = ∑ l, c l • tensorMode e (l ∘ σ.symm) := by
      intro σ
      rw [← hc, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, permActLM_prod]; rfl
    calc (∑ σ : Equiv.Perm (Fin d), permActLM σ f)
        = ∑ σ : Equiv.Perm (Fin d), ∑ l, c l • tensorMode e (l ∘ σ.symm) :=
            Finset.sum_congr rfl fun σ _ => hsub σ
      _ = ∑ σ : Equiv.Perm (Fin d), ∑ l, c (l ∘ σ) • tensorMode e l := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [← sum_comp_perm (m := m) (d := d) σ.symm
              (fun l : Fin d → Fin m => c (l ∘ σ) • tensorMode e l)]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [show (l ∘ σ.symm) ∘ σ = l from by ext i; simp]
      _ = ∑ l : Fin d → Fin m, avgCoeff c l • tensorMode e l := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [avgCoeff, Finset.sum_smul]
  -- so `f` is a combination of the labelling monomials with the *symmetrised* coefficients
  have hf_eq : f = ∑ l : Fin d → Fin m, (avgCoeff c l / (d.factorial : ℂ)) • tensorMode e l := by
    rw [hA, hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    rw [one_div, div_eq_mul_inv, mul_comm]
  -- those coefficients are constant on the fibres of the occupation map, so the sum regroups
  -- into the symmetric mode products `M_α`
  have hd : ∀ α ∈ modeMultImage m d, (α.sum fun _ k => k) = d := by
    intro α hα
    obtain ⟨l, -, heq⟩ := Finset.mem_image.mp hα
    rw [← heq]
    exact modeMult_sum' l
  refine ⟨∑ α ∈ modeMultImage m d, Finsupp.single α (symmCoeff c α *
    ((Real.sqrt (d.factorial : ℝ) : ℂ) / (Work.BoseB4.mfac α : ℂ))), ?_⟩
  exact (boxRealiseC_sum_smul_modeProd e (modeMultImage m d) (symmCoeff c) hd).trans
    ((hf_eq.trans (sum_avgCoeff_tensorMode e c)).symm)

end Work.BoseBoxFock
