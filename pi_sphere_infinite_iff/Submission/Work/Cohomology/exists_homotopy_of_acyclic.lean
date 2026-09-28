import Mathlib

/-!
# An acyclic chain complex of vector spaces is contractible

Over a field `k`, every short exact sequence of `k`-modules splits (all modules are projective),
so a chain complex of `k`-vector spaces with vanishing homology is *contractible*: the identity
chain map is homotopic to `0`.

The proof builds the null-homotopy degree by degree.  If `Hₙ(C) = 0` then the differential
`d_{n+1} : C_{n+1} → C_n` maps onto `ker d_n`, so once a section `H_{n-1} : C_{n-1} → C_n` has
been chosen, the endomorphism `1 - H_{n-1} d_n` of `C_n` kills `d_{n-1}`, hence lands in
`ker d_{n-1} = im d_n`, and since `C_n` is projective it factors through `d_n`, producing
`H_n : C_n → C_{n+1}`.  The resulting maps satisfy `d_{n+1} H_n + H_{n-1} d_n = 1`, which is
exactly the homotopy equation.  `Homotopy.mkInductive` assembles this induction into a
`Homotopy (𝟙 C) 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- **Acyclic chain complexes of vector spaces are contractible.**
If a chain complex `C` of modules over a field `k` has vanishing homology in every degree, then
its identity chain map is homotopic to the zero map. -/
theorem exists_homotopy_of_acyclic (k : Type) [Field k] (C : ChainComplex (ModuleCat k) ℕ)
    (hC : ∀ n : ℕ, CategoryTheory.Limits.IsZero (C.homology n)) :
    Nonempty (Homotopy (CategoryTheory.CategoryStruct.id C) 0) := by
  -- every `k`-module is projective (all modules over a field are free)
  haveI hproj : ∀ n : ℕ, Projective (C.X n) := fun n =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis k (C.X n))
  -- index computations for the shape `ComplexShape.down ℕ`
  have next_eq : ∀ n : ℕ, (ComplexShape.down ℕ).next n = n - 1 := by
    intro n
    cases n with
    | zero => simp [ChainComplex.next_nat_zero]
    | succ n => simp [ChainComplex.next_nat_succ]
  have prev_eq : ∀ n : ℕ, (ComplexShape.down ℕ).prev n = n + 1 := fun n => ChainComplex.prev ℕ n
  -- exactness of the short complex `C_{n+1} ⟶ C_n ⟶ C_{n-1}` in every degree
  have hExact : ∀ n : ℕ, (C.sc' (n+1) n (n-1)).Exact := fun n =>
    (C.exactAt_iff' (n+1) n (n-1) (prev_eq n) (next_eq n)).1
      ((C.exactAt_iff_isZero_homology n).2 (hC n))
  -- degree `0`: `d₁ : C₁ ⟶ C₀` is onto, hence `C₀` (projective) splits it
  have h0 : (𝟙 (C.X 0)) ≫ (C.sc' 1 0 (0-1)).g = 0 := by
    show (𝟙 (C.X 0)) ≫ C.d 0 (0-1) = 0
    have hd : C.d 0 (0-1) = 0 := C.shape 0 0 (by simp [ComplexShape.down])
    rw [hd, comp_zero]
  let zero : C.X 0 ⟶ C.X 1 := (hExact 0).liftFromProjective (𝟙 (C.X 0)) h0
  have hzero : zero ≫ C.d 1 0 = 𝟙 (C.X 0) :=
    (hExact 0).liftFromProjective_comp (𝟙 (C.X 0)) h0
  have comm_zero : (𝟙 C : C ⟶ C).f 0 = zero ≫ C.d 1 0 := by
    rw [HomologicalComplex.id_f, hzero]
  -- degree `1`: `1 - H₀ d₀` kills `d₀`, hence factors through `d₁`
  have he₁ : (𝟙 (C.X 1) - C.d 1 0 ≫ zero) ≫ (C.sc' 2 1 0).g = 0 := by
    show (𝟙 (C.X 1) - C.d 1 0 ≫ zero) ≫ C.d 1 0 = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hzero, Category.comp_id,
      sub_self]
  let one : C.X 1 ⟶ C.X 2 := (hExact 1).liftFromProjective (𝟙 (C.X 1) - C.d 1 0 ≫ zero) he₁
  have hone : one ≫ C.d 2 1 = 𝟙 (C.X 1) - C.d 1 0 ≫ zero :=
    (hExact 1).liftFromProjective_comp (𝟙 (C.X 1) - C.d 1 0 ≫ zero) he₁
  have comm_one : (𝟙 C : C ⟶ C).f 1 = C.d 1 0 ≫ zero + one ≫ C.d 2 1 := by
    rw [HomologicalComplex.id_f, hone]
    abel
  -- inductive step, assembled by `Homotopy.mkInductive`
  refine ⟨Homotopy.mkInductive (𝟙 C : C ⟶ C) zero comm_zero one comm_one ?_⟩
  rintro n ⟨f, f', hf⟩
  rw [HomologicalComplex.id_f] at hf
  -- `𝟙 = f ≫ d_n + d_{n+1} f'` gives `d_{n+1} f' = 𝟙 - f d_n`
  have hf' : f' ≫ C.d (n+2) (n+1) = 𝟙 (C.X (n+1)) - C.d (n+1) n ≫ f := by
    rw [hf]; abel
  -- thus `1 - d_{n+1} f'` kills `d_{n+1}`, so it factors through `d_{n+2}`
  have he : (𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f') ≫ (C.sc' (n+3) (n+2) (n+1)).g = 0 := by
    show (𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f') ≫ C.d (n+2) (n+1) = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hf', Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp, sub_zero,
      sub_self]
  refine ⟨(hExact (n+2)).liftFromProjective (𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f') he, ?_⟩
  have hcomp :
      (hExact (n+2)).liftFromProjective (𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f') he
          ≫ C.d (n+3) (n+2)
        = 𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f' :=
    (hExact (n+2)).liftFromProjective_comp (𝟙 (C.X (n+2)) - C.d (n+2) (n+1) ≫ f') he
  rw [HomologicalComplex.id_f, hcomp]
  abel

end Work.Cohomology
