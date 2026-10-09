import Mathlib
import Submission.Work.SSGRoute.flg_defs
import Submission.Work.SSGRoute.base_fin_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The two-letter case of the residual-generation statement

Let `A = 𝔽₂[X^*]` be the free associative `𝔽₂`-algebra on a type `X` of letters, `⁅a,b⁆ = a*b + b*a`
the commutator, `brk4 X t = ⁅⁅⁅t₁,t₂⁆,t₃⁆,t₄⁆` the degree-`4` left-nested commutator and
`Wsub X` its span.  Let `σ` be a fixed-point-free involution of `X`, `x` a letter with `σ x ≠ x`,
and `σA` the induced algebra involution of `A`.

The lemma proved here (`flg_two_letters`) is the two-letter case `{x, σ x}` of the residual
generation statement: if `u ∈ Wsub X` is `σA`-fixed and supported on words whose letters all lie in
`{x, σ x}` and which contain both `x` and `σ x`, then there is `w ∈ Wsub X` with
`u - (w + σA w) ∈ flgThetaSpan X σA`.

Only three elements of `Wsub X` can occur:  `B₀ = ⁅⁅⁅x,σx⁆,x⁆,x⁆`, `B₁ = ⁅⁅⁅x,σx⁆,x⁆,σx⁆` and
`B₂ = ⁅⁅⁅x,σx⁆,σx⁆,σx⁆`; `σA` interchanges `B₀` and `B₂`, fixes `B₁`, `B₀ + B₂ = σA B₀ + B₀ ≠ 0`
and `B₁` is the residual element `(x*x)·σA(x*x) + σA(x*x)·(x*x)`.  Hence a `σA`-fixed `u` is
`b • (B₀ + B₂) + β • B₁` and `w := b • B₀` works.

The non-vanishing `B₀ + B₂ ≠ 0` is proved by retracting the two letters `x`, `σ x` to `Fin 2`
(where it is `bftD_ne_zero`).
-/

/-- The free associative `𝔽₂`-algebra on the letters `X`. -/
abbrev flgtl_A (X : Type) : Type := MonoidAlgebra (ZMod 2) (FreeMonoid X)

/-! ## Bracket identities in characteristic two -/

theorem flgtl_brk_self (X : Type) (a : flgtl_A X) : brk X a a = 0 := by
  simp only [brk, flg_add_self]

theorem flgtl_brk_sq_left (X : Type) (a b : flgtl_A X) :
    brk X (a * a) b = brk X (brk X a b) a := by
  simp only [brk]; noncomm_ring
  simp only [two_zsmul, flg_add_self, add_zero]

/-- `⁅⁅⁅a,b⁆,b⁆,a⁆ = ⁅⁅⁅a,b⁆,a⁆,b⁆`. -/
theorem flgtl_brk_brk_swap (X : Type) (a b : flgtl_A X) :
    brk X (brk X (brk X a b) b) a = brk X (brk X (brk X a b) a) b := by
  have h := flg_brk_brk X (brk X a b) a b
  rw [flgtl_brk_self X (brk X a b)] at h
  set P := brk X (brk X (brk X a b) a) b with hP
  set Q := brk X (brk X (brk X a b) b) a with hQ
  have hsum : P + Q = 0 := h.symm
  calc Q = Q + 0 := (add_zero Q).symm
    _ = Q + (P + Q) := by rw [← hsum]
    _ = P + (Q + Q) := by abel
    _ = P + 0 := by rw [flg_add_self Q]
    _ = P := add_zero P

/-- `-t = t` in an `𝔽₂`-algebra. -/
theorem flgtl_neg_eq_self (X : Type) (t : flgtl_A X) : -t = t :=
  (eq_neg_of_add_eq_zero_left (flg_add_self t)).symm

/-! ## The two letters `x`, `σ x` -/

/-- `⁅⁅⁅x,σx⁆,x⁆,x⁆`. -/
noncomputable def flgtlB0 (X : Type) (x : X) (σ : X → X) : flgtl_A X :=
  brk4 X (x, σ x, x, x)

/-- `⁅⁅⁅x,σx⁆,x⁆,σx⁆`. -/
noncomputable def flgtlB1 (X : Type) (x : X) (σ : X → X) : flgtl_A X :=
  brk4 X (x, σ x, x, σ x)

/-- `⁅⁅⁅x,σx⁆,σx⁆,σx⁆`. -/
noncomputable def flgtlB2 (X : Type) (x : X) (σ : X → X) : flgtl_A X :=
  brk4 X (x, σ x, σ x, σ x)

theorem flgtlB0_unfold (X : Type) (x : X) (σ : X → X) :
    flgtlB0 X x σ
      = brk X (brk X (brk X (flg_ltr X x) (flg_ltr X (σ x))) (flg_ltr X x))
          (flg_ltr X x) := rfl

theorem flgtlB1_unfold (X : Type) (x : X) (σ : X → X) :
    flgtlB1 X x σ
      = brk X (brk X (brk X (flg_ltr X x) (flg_ltr X (σ x))) (flg_ltr X x))
          (flg_ltr X (σ x)) := rfl

theorem flgtlB2_unfold (X : Type) (x : X) (σ : X → X) :
    flgtlB2 X x σ
      = brk X (brk X (brk X (flg_ltr X x) (flg_ltr X (σ x))) (flg_ltr X (σ x)))
          (flg_ltr X (σ x)) := rfl

theorem flgtl_B0_mem (X : Type) (x : X) (σ : X → X) :
    flgtlB0 X x σ ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) :=
  Submodule.subset_span (by simp)

theorem flgtl_B1_mem (X : Type) (x : X) (σ : X → X) :
    flgtlB1 X x σ ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) :=
  Submodule.subset_span (by simp)

theorem flgtl_B2_mem (X : Type) (x : X) (σ : X → X) :
    flgtlB2 X x σ ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) :=
  Submodule.subset_span (by simp)

theorem flgtl_B0_mem_Wsub (X : Type) (x : X) (σ : X → X) : flgtlB0 X x σ ∈ Wsub X :=
  Submodule.subset_span ⟨(x, σ x, x, x), rfl⟩

section TwoLetters

variable {X : Type} [DecidableEq X] {x : X} {σ : X → X}

theorem flgtl_mem_pair (c : X) (hc : c ∈ ({x, σ x} : Finset X)) : c = x ∨ c = σ x := by
  simpa using hc

/-- The commutator of two distinct letters of the pair is `⁅x,σx⁆`. -/
theorem flgtl_brk_ltr_eq (c d : X) (hc : c ∈ ({x, σ x} : Finset X))
    (hd : d ∈ ({x, σ x} : Finset X)) (hcd : c ≠ d) :
    brk X (flg_ltr X c) (flg_ltr X d) = brk X (flg_ltr X x) (flg_ltr X (σ x)) := by
  rcases flgtl_mem_pair c hc with hc' | hc' <;> rcases flgtl_mem_pair d hd with hd' | hd'
  · exact absurd (hc'.trans hd'.symm) hcd
  · rw [hc', hd']
  · rw [hc', hd', flg_brk_comm]
  · exact absurd (hc'.trans hd'.symm) hcd

/-- The four elements `⁅⁅⁅x,σx⁆,c₃⁆,c₄⁆` (`c₃, c₄` letters of the pair) lie in the span of
`B₀, B₁, B₂`. -/
theorem flgtl_A_mem (u w : X) (hu : u ∈ ({x, σ x} : Finset X))
    (hw : w ∈ ({x, σ x} : Finset X)) :
    brk X (brk X (brk X (flg_ltr X x) (flg_ltr X (σ x))) (flg_ltr X u)) (flg_ltr X w)
      ∈ Submodule.span (ZMod 2)
        ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) := by
  rcases flgtl_mem_pair u hu with hu' | hu' <;> rcases flgtl_mem_pair w hw with hw' | hw'
  · rw [hu', hw', ← flgtlB0_unfold X x σ]
    exact flgtl_B0_mem X x σ
  · rw [hu', hw', ← flgtlB1_unfold X x σ]
    exact flgtl_B1_mem X x σ
  · rw [hu', hw', flgtl_brk_brk_swap X (flg_ltr X x) (flg_ltr X (σ x)),
      ← flgtlB1_unfold X x σ]
    exact flgtl_B1_mem X x σ
  · rw [hu', hw', ← flgtlB2_unfold X x σ]
    exact flgtl_B2_mem X x σ

/-- Every `⁅⁅⁅c₁,c₂⁆,c₃⁆,c₄⁆` with all `cᵢ` in `{x,σx}` lies in the span of `B₀, B₁, B₂`. -/
theorem flgtl_brk4_mem (t : X × X × X × X) (h1 : t.1 ∈ ({x, σ x} : Finset X))
    (h2 : t.2.1 ∈ ({x, σ x} : Finset X)) (h3 : t.2.2.1 ∈ ({x, σ x} : Finset X))
    (h4 : t.2.2.2 ∈ ({x, σ x} : Finset X)) :
    brk4 X t ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) := by
  obtain ⟨c1, c2, c3, c4⟩ := t
  by_cases h12 : c1 = c2
  · have hzero : brk4 X (c1, c2, c3, c4) = 0 := by
      rw [h12, flg_brk4_eq X c2 c2 c3 c4, flgtl_brk_self X (flg_ltr X c2)]
      simp only [brk, zero_mul, mul_zero, add_zero]
    rw [hzero]
    exact Submodule.zero_mem _
  · have hA : brk X (flg_ltr X c1) (flg_ltr X c2) = brk X (flg_ltr X x) (flg_ltr X (σ x)) :=
      flgtl_brk_ltr_eq c1 c2 h1 h2 h12
    rw [flg_brk4_eq X c1 c2 c3 c4, hA]
    exact flgtl_A_mem c3 c4 h3 h4

/-- The letter-set projection onto `{x,σx}` of a generator lies in the span of `B₀, B₁, B₂`. -/
theorem flgtl_proj_brk4_mem (t : X × X × X × X) :
    flg_proj X ({x, σ x} : Finset X) (brk4 X t) ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) := by
  rw [flg_proj_brk4]
  split_ifs with h
  · refine flgtl_brk4_mem t ?_ ?_ ?_ ?_ <;> · rw [← h]; simp [flg_letters4]
  · exact Submodule.zero_mem _

/-- The projection onto `{x,σx}` is the identity on elements supported there. -/
theorem flgtl_proj_eq_self (v : flgtl_A X)
    (hs : ∀ w : FreeMonoid X, v.coeff w ≠ 0 → flg_letters w = ({x, σ x} : Finset X)) :
    flg_proj X ({x, σ x} : Finset X) v = v := by
  ext w
  rw [flg_proj_apply]
  by_cases h : flg_letters w = ({x, σ x} : Finset X)
  · simp only [h, if_true]
  · rw [if_neg h, eq_comm]
    by_contra hc
    exact h (hs w hc)

/-- An element of `Wsub X` supported on the letter set `{x,σx}` lies in the span of `B₀, B₁, B₂`. -/
theorem flgtl_mem_span_of_support (v : flgtl_A X) (hv : v ∈ Wsub X)
    (hs : ∀ w : FreeMonoid X, v.coeff w ≠ 0 → flg_letters w = ({x, σ x} : Finset X)) :
    v ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) := by
  have hmap : Submodule.map (flg_proj X ({x, σ x} : Finset X)) (Wsub X)
      ≤ Submodule.span (ZMod 2)
        ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) := by
    rw [Wsub, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨z, ⟨t, rfl⟩, rfl⟩
    exact flgtl_proj_brk4_mem t
  have hmem : flg_proj X ({x, σ x} : Finset X) v ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x σ, flgtlB1 X x σ, flgtlB2 X x σ} : Set (flgtl_A X)) :=
    hmap (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  rwa [flgtl_proj_eq_self v hs] at hmem

end TwoLetters

/-! ## The action of `σA` on the three generators -/

section Sigma

variable {X : Type} {x : X} {σ : X ≃ X}

theorem flgtl_sigmaA_B0 (hσ : ∀ y, σ (σ y) = y)
    (σA : flgtl_A X →ₗ[ZMod 2] flgtl_A X)
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) :
    σA (flgtlB0 X x σ) = flgtlB2 X x σ := by
  rw [show flgtlB0 X x σ = brk4 X (x, σ x, x, x) from rfl,
      show flgtlB2 X x σ = brk4 X (x, σ x, σ x, σ x) from rfl,
      flg_sigmaA_brk4 X (fun y => σ y) σA hmul hone hgen x (σ x) x x, hσ x]
  exact flg_brk4_symm X (σ x) x (σ x) (σ x)

theorem flgtl_sigmaA_B2 (hσ : ∀ y, σ (σ y) = y)
    (σA : flgtl_A X →ₗ[ZMod 2] flgtl_A X)
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) :
    σA (flgtlB2 X x σ) = flgtlB0 X x σ := by
  rw [show flgtlB2 X x σ = brk4 X (x, σ x, σ x, σ x) from rfl,
      show flgtlB0 X x σ = brk4 X (x, σ x, x, x) from rfl,
      flg_sigmaA_brk4 X (fun y => σ y) σA hmul hone hgen x (σ x) (σ x) (σ x), hσ x]
  exact flg_brk4_symm X (σ x) x x x

theorem flgtl_sigmaA_B1 (hσ : ∀ y, σ (σ y) = y)
    (σA : flgtl_A X →ₗ[ZMod 2] flgtl_A X)
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) :
    σA (flgtlB1 X x σ) = flgtlB1 X x σ := by
  rw [show flgtlB1 X x σ = brk4 X (x, σ x, x, σ x) from rfl,
      flg_sigmaA_brk4 X (fun y => σ y) σA hmul hone hgen x (σ x) x (σ x), hσ x,
      flg_brk4_symm X (σ x) x (σ x) x, flg_brk4_eq X x (σ x) (σ x) x,
      flg_brk4_eq X x (σ x) x (σ x)]
  exact flgtl_brk_brk_swap X (flg_ltr X x) (flg_ltr X (σ x))

/-- `B₁` is the residual element attached to `x * x ∈ Tsub X`. -/
theorem flgtl_B1_theta (σA : flgtl_A X →ₗ[ZMod 2] flgtl_A X)
    (hmul : ∀ a b, σA (a * b) = σA a * σA b)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) :
    flgtlB1 X x σ = (flg_ltr X x * flg_ltr X x) * σA (flg_ltr X x * flg_ltr X x)
      + σA (flg_ltr X x * flg_ltr X x) * (flg_ltr X x * flg_ltr X x) := by
  have hσsq : σA (flg_ltr X x * flg_ltr X x) = flg_ltr X (σ x) * flg_ltr X (σ x) := by
    rw [hmul, hgen x]
  rw [hσsq, show flgtlB1 X x σ = brk4 X (x, σ x, x, σ x) from rfl, flg_brk4_eq,
    ← flgtl_brk_sq_left X (flg_ltr X x) (flg_ltr X (σ x))]
  rw [flg_brk_comm X ((flg_ltr X x) * (flg_ltr X x)) (flg_ltr X (σ x))]
  rw [← flgtl_brk_sq_left X (flg_ltr X (σ x)) ((flg_ltr X x) * (flg_ltr X x)),
    flg_brk_comm X ((flg_ltr X (σ x)) * (flg_ltr X (σ x)))
      ((flg_ltr X x) * (flg_ltr X x))]
  rfl

/-- `x * x ∈ Tsub X`. -/
theorem flgtl_ltr_sq_mem_Tsub (x : X) : flg_ltr X x * flg_ltr X x ∈ Tsub X := by
  have h : (fun p : X × X =>
      MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
        * MonoidAlgebra.single (FreeMonoid.of p.1) 1
      + (MonoidAlgebra.single (FreeMonoid.of p.2) 1
          * MonoidAlgebra.single (FreeMonoid.of p.1) 1
        + MonoidAlgebra.single (FreeMonoid.of p.1) 1
          * MonoidAlgebra.single (FreeMonoid.of p.2) 1)) (x, x)
      = flg_ltr X x * flg_ltr X x := by
    simp only [flg_ltr, flg_add_self, add_zero]
  rw [Tsub, ← h]
  exact Submodule.subset_span ⟨(x, x), rfl⟩

/-- `B₁` lies in the residual span. -/
theorem flgtl_B1_mem_theta (σA : flgtl_A X →ₗ[ZMod 2] flgtl_A X)
    (hmul : ∀ a b, σA (a * b) = σA a * σA b)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) :
    flgtlB1 X x σ ∈ flgThetaSpan X σA := by
  rw [flgtl_B1_theta σA hmul hgen]
  exact Submodule.subset_span ⟨⟨flg_ltr X x * flg_ltr X x, flgtl_ltr_sq_mem_Tsub x⟩, rfl⟩

end Sigma

/-! ## Non-vanishing of `B₀ + B₂`, by retraction to the two letters `0`, `1` of `Fin 2` -/

section Retr

/-- The algebra map `A(X) → A(Fin 2)` sending `x ↦ 0`, `σ x ↦ 1` and all other letters to `0`. -/
noncomputable def flgtlRetr (X : Type) [DecidableEq X] (x : X) (σ : X → X) :
    flgtl_A X →ₐ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  MonoidAlgebra.lift (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) (FreeMonoid X)
    (FreeMonoid.lift fun y : X =>
      if y = x then MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 2)) (FreeMonoid.of (0 : Fin 2))
      else if y = σ x then
        MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 2)) (FreeMonoid.of (1 : Fin 2)) else 0)

theorem flgtlRetr_apply_ltr (X : Type) [DecidableEq X] (x : X) (σ : X → X) (y : X) :
    flgtlRetr X x σ (flg_ltr X y) =
      (if y = x then MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 2)) (FreeMonoid.of (0 : Fin 2))
       else if y = σ x then
        MonoidAlgebra.of (ZMod 2) (FreeMonoid (Fin 2)) (FreeMonoid.of (1 : Fin 2)) else 0) := by
  simp only [flg_ltr, ← MonoidAlgebra.of_apply (ZMod 2) (FreeMonoid X), flgtlRetr,
    MonoidAlgebra.lift_of, FreeMonoid.lift_eval_of]

theorem flgtlRetr_ltr_self (X : Type) [DecidableEq X] (x : X) (σ : X → X) :
    flgtlRetr X x σ (flg_ltr X x) = MonoidAlgebra.single (FreeMonoid.of (0 : Fin 2)) 1 := by
  rw [flgtlRetr_apply_ltr X x σ x, if_pos rfl, MonoidAlgebra.of_apply]

theorem flgtlRetr_ltr_sigma (X : Type) [DecidableEq X] (x : X) (σ : X → X)
    (hfree : σ x ≠ x) :
    flgtlRetr X x σ (flg_ltr X (σ x)) =
      MonoidAlgebra.single (FreeMonoid.of (1 : Fin 2)) 1 := by
  rw [flgtlRetr_apply_ltr X x σ (σ x), if_neg hfree, if_pos rfl, MonoidAlgebra.of_apply]

theorem flgtlRetr_brk4 (X : Type) [DecidableEq X] (x : X) (σ : X → X)
    (t : X × X × X × X) :
    flgtlRetr X x σ (brk4 X t) =
      brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (flgtlRetr X x σ (flg_ltr X t.1))
        (flgtlRetr X x σ (flg_ltr X t.2.1))) (flgtlRetr X x σ (flg_ltr X t.2.2.1)))
        (flgtlRetr X x σ (flg_ltr X t.2.2.2)) := by
  simp only [brk4, brk, flg_ltr, map_add, map_mul]

theorem flgtlRetr_B0 (X : Type) [DecidableEq X] (x : X) (σ : X → X) (hfree : σ x ≠ x) :
    flgtlRetr X x σ (flgtlB0 X x σ) = bftB0 := by
  rw [show flgtlB0 X x σ = brk4 X (x, σ x, x, x) from rfl, flgtlRetr_brk4,
    flgtlRetr_ltr_self, flgtlRetr_ltr_sigma X x σ hfree]
  rfl

theorem flgtlRetr_B2 (X : Type) [DecidableEq X] (x : X) (σ : X → X) (hfree : σ x ≠ x) :
    flgtlRetr X x σ (flgtlB2 X x σ) = bftB2 := by
  rw [show flgtlB2 X x σ = brk4 X (x, σ x, σ x, σ x) from rfl, flgtlRetr_brk4,
    flgtlRetr_ltr_self, flgtlRetr_ltr_sigma X x σ hfree]
  rfl

theorem flgtl_pair_sum_ne_zero (X : Type) [DecidableEq X] (x : X) (σ : X → X)
    (hfree : σ x ≠ x) : flgtlB0 X x σ + flgtlB2 X x σ ≠ 0 := by
  intro h0
  have hmap : flgtlRetr X x σ (flgtlB0 X x σ) + flgtlRetr X x σ (flgtlB2 X x σ) = 0 := by
    rw [← map_add, h0, map_zero]
  rw [flgtlRetr_B0 X x σ hfree, flgtlRetr_B2 X x σ hfree] at hmap
  exact bftD_ne_zero hmap

end Retr

/-! ## The two-letter case -/

theorem flg_two_letters (X : Type) [DecidableEq X] (x : X) (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y)
    (hfree : σ x ≠ x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1)
    (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hu : u ∈ Wsub X) (hfix : σA u = u)
    (hsupp : ∀ w : FreeMonoid X, u.coeff w ≠ 0 →
      (∀ y ∈ w.toList, y = x ∨ y = σ x) ∧ x ∈ w.toList ∧ σ x ∈ w.toList) :
    ∃ w ∈ Wsub X, u - (w + σA w) ∈ flgThetaSpan X σA := by
  classical
  have hs : ∀ w : FreeMonoid X, u.coeff w ≠ 0 → flg_letters w = ({x, σ x} : Finset X) := by
    intro w hw
    obtain ⟨hlet, hx, hsx⟩ := hsupp w hw
    ext y
    simp only [flg_letters, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hy => hlet y hy, fun hy => hy.elim (fun h => h.symm ▸ hx) (fun h => h.symm ▸ hsx)⟩
  have hspan : u ∈ Submodule.span (ZMod 2)
      ({flgtlB0 X x (fun y => σ y), flgtlB1 X x (fun y => σ y), flgtlB2 X x (fun y => σ y)} :
        Set (flgtl_A X)) :=
    flgtl_mem_span_of_support u hu hs
  obtain ⟨a, z, hz, hva⟩ := (Submodule.mem_span_insert).mp hspan
  obtain ⟨b, c, hbc⟩ := (Submodule.mem_span_pair).mp hz
  have hσ0 : σA (flgtlB0 X x (fun y => σ y)) = flgtlB2 X x (fun y => σ y) :=
    flgtl_sigmaA_B0 hσ σA hmul hone hgen
  have hσ1 : σA (flgtlB1 X x (fun y => σ y)) = flgtlB1 X x (fun y => σ y) :=
    flgtl_sigmaA_B1 hσ σA hmul hone hgen
  have hσ2 : σA (flgtlB2 X x (fun y => σ y)) = flgtlB0 X x (fun y => σ y) :=
    flgtl_sigmaA_B2 hσ σA hmul hone hgen
  have hu_eq : u = a • flgtlB0 X x (fun y => σ y)
      + (b • flgtlB1 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y)) := by
    rw [hva, hbc]
  have hσu : σA u = a • flgtlB2 X x (fun y => σ y)
      + (b • flgtlB1 X x (fun y => σ y) + c • flgtlB0 X x (fun y => σ y)) := by
    rw [hu_eq, map_add, map_add, map_smul, map_smul, map_smul, hσ0, hσ1, hσ2]
  have hsum : u + σA u
      = (a + c) • (flgtlB0 X x (fun y => σ y) + flgtlB2 X x (fun y => σ y)) := by
    rw [hσu, hu_eq]
    rw [show a • flgtlB0 X x (fun y => σ y)
          + (b • flgtlB1 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y))
          + (a • flgtlB2 X x (fun y => σ y)
            + (b • flgtlB1 X x (fun y => σ y) + c • flgtlB0 X x (fun y => σ y)))
        = (a • flgtlB0 X x (fun y => σ y) + c • flgtlB0 X x (fun y => σ y))
          + (b • flgtlB1 X x (fun y => σ y) + b • flgtlB1 X x (fun y => σ y))
          + (a • flgtlB2 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y)) from by abel]
    rw [flg_add_self (b • flgtlB1 X x (fun y => σ y)), add_zero, ← add_smul, ← add_smul,
      ← smul_add]
  have hzero : (a + c) • (flgtlB0 X x (fun y => σ y) + flgtlB2 X x (fun y => σ y)) = 0 := by
    rw [← hsum, hfix]
    exact flg_add_self u
  have hne : flgtlB0 X x (fun y => σ y) + flgtlB2 X x (fun y => σ y) ≠ 0 :=
    flgtl_pair_sum_ne_zero X x (fun y => σ y) hfree
  have hac : a + c = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hne
  refine ⟨c • flgtlB0 X x (fun y => σ y), Submodule.smul_mem _ c
    (flgtl_B0_mem_Wsub X x (fun y => σ y)), ?_⟩
  have hres : u - (c • flgtlB0 X x (fun y => σ y) + σA (c • flgtlB0 X x (fun y => σ y)))
      = b • flgtlB1 X x (fun y => σ y) := by
    rw [map_smul, hσ0, sub_eq_add_neg, flgtl_neg_eq_self, hu_eq]
    rw [show a • flgtlB0 X x (fun y => σ y)
          + (b • flgtlB1 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y))
          + (c • flgtlB0 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y))
        = (a • flgtlB0 X x (fun y => σ y) + c • flgtlB0 X x (fun y => σ y))
          + (c • flgtlB2 X x (fun y => σ y) + c • flgtlB2 X x (fun y => σ y))
          + b • flgtlB1 X x (fun y => σ y) from by abel]
    rw [flg_add_self (c • flgtlB2 X x (fun y => σ y)), add_zero, ← add_smul, hac, zero_smul,
      zero_add]
  rw [hres]
  exact Submodule.smul_mem _ b (flgtl_B1_mem_theta σA hmul hgen)

end Work.SSGRoute
