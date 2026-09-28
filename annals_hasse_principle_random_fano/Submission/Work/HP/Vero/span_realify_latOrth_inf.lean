import Mathlib
import Submission.Work.HP.Vero

/-!
# The real span of the integer points of `Λ_v ∩ Λ_w`

The main result of this file is `Work.HP.Vero.span_realify_latOrth_inf`: the integer points of the
orthogonal complement of `span{v,w}` (i.e. of the lattice `Λ_v ∩ Λ_w ⊆ ℤ^ι`) span, over `ℝ`, the
simultaneous kernel of the two real functionals `x ↦ ∑ i, x i • v i` and `x ↦ ∑ i, x i • w i`.

The proof has two ingredients.

* `finrank_span_image_intCastPi`: for *every* `ℤ`-submodule `K ⊆ ℤ^ι` the real dimension of the span
  of its image under `intCastPi` equals the `ℤ`-rank of `K`.  This is the "saturated sublattice"
  content: a `ℤ`-basis of `K` is `ℤ`-independent, hence `ℝ`-independent after casting (Mathlib's
  `linearIndependent_algebraMap_comp_iff`), and it spans the left hand side.
* rank–nullity, over `ℤ` and over `ℝ`, for the pair map `x ↦ (⟨v,x⟩, ⟨w,x⟩)`; the ranges have the
  same dimension in the two settings by `finrank_span_image_intCastPi` again (applied on the
  `Fin 2 → ℤ` side).
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

/-! ## The evaluation map of a pair of vectors -/

/-- The `R`-linear map `x ↦ (∑ i, x i • c i, ∑ i, x i • d i)`, as a `Fin 2`-indexed family. -/
def pairMap {ι : Type*} [Fintype ι] (R : Type*) [Semiring R] (c d : ι → R) :
    (ι → R) →ₗ[R] (Fin 2 → R) where
  toFun x := ![Fintype.linearCombination R c x, Fintype.linearCombination R d x]
  map_add' x y := by ext j; fin_cases j <;> simp
  map_smul' a x := by ext j; fin_cases j <;> simp

lemma mem_ker_pairMap_iff {ι : Type*} [Fintype ι] {R : Type*} [Semiring R] {c d : ι → R}
    {x : ι → R} :
    x ∈ LinearMap.ker (pairMap R c d) ↔
      Fintype.linearCombination R c x = 0 ∧ Fintype.linearCombination R d x = 0 := by
  simp [LinearMap.mem_ker, pairMap, funext_iff, Fin.forall_fin_two]

/-- `Λ_v ∩ Λ_w` is the kernel of the pair map `x ↦ (⟨v,x⟩, ⟨w,x⟩)` over `ℤ`. -/
lemma ker_pairMap_int {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    LinearMap.ker (pairMap ℤ v w) = latOrth v ⊓ latOrth w := by
  ext x
  rw [mem_ker_pairMap_iff, Submodule.mem_inf, latOrth, latOrth, LinearMap.mem_ker,
    LinearMap.mem_ker]

/-- The same, over `ℝ`. -/
lemma ker_pairMap_real {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    LinearMap.ker (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ)))
      = LinearMap.ker (Fintype.linearCombination ℝ (fun i => (v i : ℝ)))
        ⊓ LinearMap.ker (Fintype.linearCombination ℝ (fun i => (w i : ℝ))) := by
  ext x
  rw [mem_ker_pairMap_iff, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]

/-- The pair map commutes with the change of scalars `ℤ → ℝ`. -/
lemma intCastPi_pairMap {ι : Type*} [Fintype ι] (v w : ι → ℤ) (x : ι → ℤ) :
    intCastPi (pairMap ℤ v w x)
      = pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ)) (intCastPi x) := by
  ext j
  fin_cases j <;> simp [pairMap, Fintype.linearCombination_apply]

/-! ## Integer vectors and linear independence -/

/-- Integer vectors that are `ℤ`-linearly independent are `ℝ`-linearly independent. -/
lemma linInd_intCastPi {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] {b : κ → (ι → ℤ)}
    (hb : LinearIndependent ℤ b) : LinearIndependent ℝ (fun j => intCastPi (b j)) := by
  have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (ι' := ι) (v := b)).mpr hb
  have hfun : (fun j => intCastPi (b j)) = (fun i => ⇑(algebraMap ℤ ℝ) ∘ b i) := by
    funext j i
    rfl
  rwa [hfun]

/-- The real dimension of the span of the image of a `ℤ`-submodule `K ⊆ ℤ^ι` equals the `ℤ`-rank
of `K`. -/
lemma finrank_span_image_intCastPi {ι : Type*} [Fintype ι] (K : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℝ (Submodule.span ℝ (intCastPi '' (K : Set (ι → ℤ)))) = Module.finrank ℤ K := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) K
  have hK : K = Submodule.span ℤ (Set.range fun j : Fin n => ((b j : K) : ι → ℤ)) := by
    conv_lhs => rw [← Submodule.range_subtype K, ← Submodule.map_top]
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span ℝ (intCastPi '' (K : Set (ι → ℤ)))
      = Submodule.span ℝ (Set.range fun j : Fin n => intCastPi ((b j : K) : ι → ℤ)) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro y ⟨k, hk, rfl⟩
      let S : Submodule ℝ (ι → ℝ) :=
        Submodule.span ℝ (Set.range fun j : Fin n => intCastPi ((b j : K) : ι → ℤ))
      let T : Submodule ℤ (ι → ℤ) :=
        { carrier := {x | intCastPi x ∈ S}
          zero_mem' := by show intCastPi (0 : ι → ℤ) ∈ S; simp
          add_mem' := by
            intro x y hx hy
            show intCastPi (x + y) ∈ S
            rw [map_add]; exact add_mem hx hy
          smul_mem' := by
            intro c x hx
            show intCastPi (c • x) ∈ S
            rw [map_smul, ← Int.cast_smul_eq_zsmul ℝ c (intCastPi x)]
            exact Submodule.smul_mem _ _ hx }
      have hle : K ≤ T := by
        rw [hK]
        refine Submodule.span_le.mpr ?_
        rintro y ⟨j, rfl⟩
        show intCastPi ((b j : K) : ι → ℤ) ∈ S
        exact Submodule.subset_span (Set.mem_range_self j)
      have h2 := hle hk
      change intCastPi k ∈ S at h2
      exact h2
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(b j : K), (b j).2, rfl⟩
  rw [hspan]
  have hind : LinearIndependent ℝ (fun j : Fin n => intCastPi ((b j : K) : ι → ℤ)) := by
    apply linInd_intCastPi
    exact b.linearIndependent.map' (Submodule.subtype K) (by
      rw [LinearMap.ker_eq_bot]; exact Subtype.coe_injective)
  rw [finrank_span_eq_card hind]
  exact (Module.finrank_eq_card_basis b).symm

/-- The real span of the image of the range of the pair map is the range of the real pair map. -/
lemma span_range_pairMap {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    Submodule.span ℝ (intCastPi '' (LinearMap.range (pairMap ℤ v w) : Set (Fin 2 → ℤ)))
      = LinearMap.range (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ))) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := hz
    rw [intCastPi_pairMap]
    exact ⟨intCastPi x, rfl⟩
  · rintro y ⟨x, rfl⟩
    have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
      conv_lhs => rw [← (Pi.basisFun ℝ ι).sum_repr x]
      simp [Pi.basisFun_repr, Pi.basisFun_apply]
    have hsingle_cast (i : ι) : intCastPi (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsingle : pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ)) (Pi.single i (1 : ℝ))
        = intCastPi (pairMap ℤ v w (Pi.single i (1 : ℤ))) := by
      rw [← hsingle_cast i, intCastPi_pairMap]
    rw [map_smul, hsingle]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Pi.single i (1 : ℤ), rfl⟩, rfl⟩)

/-- The integer points of the orthogonal complement of `span{v,w}` span it over `ℝ`.

`K = latOrth v ⊓ latOrth w = {k : ι → ℤ | ∑ i, v i * k i = 0 ∧ ∑ i, w i * k i = 0}` is a
saturated (`isSat`) sublattice of `ℤ^ι`; the statement says the real span of its image under
`intCastPi : (ι → ℤ) →ₗ[ℤ] (ι → ℝ)` is the simultaneous kernel of the two real functionals
`x ↦ ∑ i, v i * x i`, `x ↦ ∑ i, w i * x i`.  `⊆` is immediate; `⊇` is the content.

Suggested route for `⊇`: let `K_ℚ = ker f_ℚ ⊆ ℚ^ι` with `f_ℚ z = (∑ v i * z i, ∑ w i * z i)`.
Then `span_ℝ (K_ℚ ↪ ℝ^ι) = ker f_ℝ` (kernel commutes with the field extension ℚ → ℝ, e.g. by
comparing dimensions via rank-nullity over ℚ), and a ℚ-subspace of `ℚ^ι` is spanned over ℚ by its
integer points (take a ℚ-basis and clear denominators), i.e. `span_ℚ K_ℚ = span_ℚ (K ↪ ℚ^ι)`;
combining gives the result.  Alternative: `Submodule.basisOfPid` gives a ℤ-basis of `K`, whose image
under `intCastPi` is ℝ-independent (ℤ-independent integer vectors are ℚ- and hence ℝ-independent)
and ℝ-spans the left-hand side; then compare `finrank`s over ℝ using
`finrank ℤ (ι → ℤ) = finrank ℤ K + finrank ℤ (range f_ℤ)`. -/
theorem span_realify_latOrth_inf {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    Submodule.span ℝ
        (((Work.HP.latOrth v ⊓ Work.HP.latOrth w : Submodule ℤ (ι → ℤ)).map
            Work.HP.intCastPi : Submodule ℤ (ι → ℝ)) : Set (ι → ℝ))
      = LinearMap.ker (Fintype.linearCombination ℝ (fun i => (v i : ℝ)))
        ⊓ LinearMap.ker (Fintype.linearCombination ℝ (fun i => (w i : ℝ))) := by
  classical
  -- rank–nullity over `ℤ`
  have hZ : Module.finrank ℤ (LinearMap.range (pairMap ℤ v w))
      + Module.finrank ℤ (LinearMap.ker (pairMap ℤ v w)) = Fintype.card ι := by
    have h := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker (pairMap ℤ v w))
    rw [(LinearMap.quotKerEquivRange (pairMap ℤ v w)).finrank_eq,
      Module.finrank_fintype_fun_eq_card] at h
    exact h
  -- rank–nullity over `ℝ`
  have hR : Module.finrank ℝ
        (LinearMap.range (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ))))
      + Module.finrank ℝ
        (LinearMap.ker (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ))))
        = Fintype.card ι := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]
  -- the two ranges have the same dimension
  have hdim_range : Module.finrank ℝ
        (LinearMap.range (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ))))
      = Module.finrank ℤ (LinearMap.range (pairMap ℤ v w)) := by
    rw [← span_range_pairMap v w]
    exact finrank_span_image_intCastPi (LinearMap.range (pairMap ℤ v w))
  -- hence so do the two kernels
  have key : Module.finrank ℤ (LinearMap.ker (pairMap ℤ v w))
      = Module.finrank ℝ
        (LinearMap.ker (pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ)))) := by
    omega
  rw [← ker_pairMap_real v w, ← ker_pairMap_int v w]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · -- `⊆`: the image of an integer solution is a real solution
    rw [Submodule.span_le]
    rintro y ⟨k, hk, rfl⟩
    change pairMap ℤ v w k = 0 at hk
    change pairMap ℝ (fun i => (v i : ℝ)) (fun i => (w i : ℝ)) (intCastPi k) = 0
    rw [← intCastPi_pairMap, hk, map_zero]
  · rw [Submodule.map_coe, finrank_span_image_intCastPi, key]

end Work.HP.Vero
