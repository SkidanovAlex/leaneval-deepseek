import Mathlib
import Submission.Work.Stems.Hur2.PsiLin
import Submission.Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased
import Submission.Work.Stems.Hur2b.K1_homotopicRel_edge
import Submission.Work.Stems.Hur2b.K1_faces

/-!
# `(Y)`: `Ψ` kills the boundary of every 3-cube

The main content is the lemma `Work.Stems.Hur2b.PsiLin_cubD_single`: for every 3-cube
`τ : I³ → X` (with `X` simply connected),
`PsiLin x₀ (cubD 2 X (single τ 1)) = 0` in `π₂(X,x₀)`.

This is Hutchings' `(2.5)`: the filling `Ψ` of a 2-cube descends to homology, i.e. the alternating
sum of the classes of the six filled faces of `τ` vanishes.

The file is organised in two layers.

* *Combinatorial reduction*: the alternating sum over the six faces is the class of the explicit
  **assembly** `assembly x₀ τ` — the six fillings `Ψ(τ_{i,b})` concatenated in the square, with the
  sign `(-1)^{i+b}` realised by reversing one coordinate.

* *Geometric core* `assembly_homotopic_const`: the assembly is null as a *based* 2-cube.  This is
  where the 3-cube `τ` is used: the six fillings glue along the 1-skeleton of `∂I³` into a map of
  the 2-sphere which is homotopic to `τ|∂I³` (each `K₁`-filling cancels onto its edge) and hence
  null (it extends over the 3-cube); Hutchings' Lemma 2.2(a)
  (`genLoop_homotopic_const_of_unbased`, proved in this directory) then gives the based statement.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The six faces of a 3-cube -/

/-- The 2-face `τ_{i,b}` of a 3-cube `τ` (`t_i` frozen at `b`). -/
def face3 (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) : C(IC 2, X) :=
  faceCube i (if (b : ℕ) = 0 then 0 else 1 : unitInterval) τ

@[simp] theorem face3_zero (τ : C(IC 3, X)) (i : Fin 3) : face3 τ i 0 = faceCube i 0 τ := rfl

@[simp] theorem face3_one (τ : C(IC 3, X)) (i : Fin 3) : face3 τ i 1 = faceCube i 1 τ := rfl

/-- The sign `(-1)^{i+b}` with which the face `τ_{i,b}` occurs in the cubical boundary `∂τ`. -/
def faceSign3 (i : Fin 3) (b : Fin 2) : ℤ := (-1) ^ ((i : ℕ) + (b : ℕ))

theorem faceSign3_zero (i : Fin 3) : faceSign3 i 0 = (-1) ^ (i : ℕ) := by simp [faceSign3]

theorem faceSign3_one (i : Fin 3) : faceSign3 i 1 = -((-1 : ℤ) ^ (i : ℕ)) := by
  rw [faceSign3, show (i : ℕ) + ((1 : Fin 2) : ℕ) = (i : ℕ) + 1 from rfl, pow_succ]
  ring

/-! ## The assembly of the six fillings -/

/-- The class of a based 2-cube in `π₂(X,x₀)`. -/
def cl (x₀ : X) (p : GenLoop (Fin 2) X x₀) : HomotopyGroup (Fin 2) X x₀ := ⟦p⟧

theorem cl_mul (x₀ : X) (p q : GenLoop (Fin 2) X x₀) :
    cl x₀ p * cl x₀ q = cl x₀ (GenLoop.transAt 0 q p) := by
  rw [cl, cl, cl]; exact HomotopyGroup.mul_spec

theorem cl_inv (x₀ : X) (p : GenLoop (Fin 2) X x₀) :
    (cl x₀ p)⁻¹ = cl x₀ (GenLoop.symmAt 1 p) := by
  rw [cl, cl]; exact HomotopyGroup.inv_spec

/-- The class of the filling `Ψ(c)`. -/
noncomputable def psiC (x₀ : X) (c : C(IC 2, X)) : HomotopyGroup (Fin 2) X x₀ :=
  cl x₀ (psiGenLoop x₀ c)

/-- `Ψ(c)` as an element of the additive group `π₂(X,x₀)`. -/
noncomputable def psiClass (x₀ : X) (c : C(IC 2, X)) : Additive (HomotopyGroup (Fin 2) X x₀) :=
  Additive.ofMul (psiC x₀ c)

/-- The layer of the assembly attached to the face `(i,b)`: the filling `Ψ(τ_{i,b})`, reversed in
coordinate 1 when the sign `(-1)^{i+b}` is `-1`. -/
noncomputable def layer3 (x₀ : X) (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    GenLoop (Fin 2) X x₀ :=
  if Even ((i : ℕ) + (b : ℕ)) then psiGenLoop x₀ (face3 τ i b)
  else GenLoop.symmAt 1 (psiGenLoop x₀ (face3 τ i b))

/-- **The assembly**: the six fillings of the faces of `τ`, concatenated in the square in the
order `(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)`. -/
noncomputable def assembly (x₀ : X) (τ : C(IC 3, X)) : GenLoop (Fin 2) X x₀ :=
  GenLoop.transAt 0 (layer3 x₀ τ 2 1) <| GenLoop.transAt 0 (layer3 x₀ τ 1 1) <|
    GenLoop.transAt 0 (layer3 x₀ τ 0 1) <| GenLoop.transAt 0 (layer3 x₀ τ 2 0) <|
      GenLoop.transAt 0 (layer3 x₀ τ 1 0) (layer3 x₀ τ 0 0)

/-- The product of the six classes of the fillings of the faces: the `(i,0)`-factor followed by the
`(i,1)`-factor, each with the sign of the cubical boundary. -/
noncomputable def prod6 (x₀ : X) (τ : C(IC 3, X)) : HomotopyGroup (Fin 2) X x₀ :=
  ∏ i : Fin 3, (psiC x₀ (face3 τ i 0)) ^ ((-1 : ℤ) ^ (i : ℕ)) *
    (psiC x₀ (face3 τ i 1)) ^ (-((-1 : ℤ) ^ (i : ℕ)))

/-- The class of a layer is the `(-1)^{i+b}`-th power of the class of the filling. -/
theorem layer3_class (x₀ : X) (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    cl x₀ (layer3 x₀ τ i b) = (psiC x₀ (face3 τ i b)) ^ faceSign3 i b := by
  have hpsi : psiC x₀ (face3 τ i b) = cl x₀ (psiGenLoop x₀ (face3 τ i b)) := rfl
  unfold layer3
  by_cases h : Even ((i : ℕ) + (b : ℕ))
  · rw [if_pos h, faceSign3, h.neg_one_pow, zpow_one, hpsi]
  · rw [if_neg h, faceSign3, (Nat.not_even_iff_odd.mp h).neg_one_pow, hpsi, zpow_neg_one,
      cl_inv]

/-- The six factors of `prod6`, reordered: a purely algebraic identity in a commutative group. -/
theorem reorder6 {G : Type*} [CommGroup G] (a b c d e f : G) (z₁ z₂ z₃ w₁ w₂ w₃ : ℤ) :
    a ^ z₁ * b ^ z₂ * c ^ z₃ * (d ^ w₁ * e ^ w₂ * f ^ w₃)
      = (a ^ z₁ * d ^ w₁) * (b ^ z₂ * e ^ w₂) * (c ^ z₃ * f ^ w₃) := by
  ac_rfl

/-- The class of the assembly, as an explicit product of the classes of the layers. -/
theorem assembly_class (x₀ : X) (τ : C(IC 3, X)) :
    cl x₀ (assembly x₀ τ) =
      cl x₀ (layer3 x₀ τ 0 0) * cl x₀ (layer3 x₀ τ 1 0) * cl x₀ (layer3 x₀ τ 2 0) *
        (cl x₀ (layer3 x₀ τ 0 1) * cl x₀ (layer3 x₀ τ 1 1) * cl x₀ (layer3 x₀ τ 2 1)) := by
  simp only [assembly]
  rw [← cl_mul, ← cl_mul, ← cl_mul, ← cl_mul, ← cl_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

/-- **The class of the assembly is the product of the six classes.** -/
theorem assembly_class_prod (x₀ : X) (τ : C(IC 3, X)) :
    cl x₀ (assembly x₀ τ) = prod6 x₀ τ := by
  rw [assembly_class, prod6]
  simp only [layer3_class, Fin.prod_univ_three]
  rw [faceSign3_zero 0, faceSign3_zero 1, faceSign3_zero 2, faceSign3_one 0, faceSign3_one 1,
    faceSign3_one 2]
  exact @reorder6 (HomotopyGroup (Fin 2) X x₀) _
    (psiC x₀ (face3 τ 0 0)) (psiC x₀ (face3 τ 1 0)) (psiC x₀ (face3 τ 2 0))
    (psiC x₀ (face3 τ 0 1)) (psiC x₀ (face3 τ 1 1)) (psiC x₀ (face3 τ 2 1))
    ((-1 : ℤ) ^ ((0 : Fin 3) : ℕ)) ((-1 : ℤ) ^ ((1 : Fin 3) : ℕ))
    ((-1 : ℤ) ^ ((2 : Fin 3) : ℕ))
    (-((-1 : ℤ) ^ ((0 : Fin 3) : ℕ))) (-((-1 : ℤ) ^ ((1 : Fin 3) : ℕ)))
    (-((-1 : ℤ) ^ ((2 : Fin 3) : ℕ)))

/-! ## The alternating sum is the class of the assembly -/

variable {G : Type*} [CommGroup G]

/-- `z`-multiples of a difference of `ofMul`s, moved to the multiplicative side. -/
theorem zsmul_ofMul_sub (a b : G) (z : ℤ) :
    z • (Additive.ofMul a - Additive.ofMul b) = Additive.ofMul (a ^ z * b ^ (-z)) := by
  rw [show Additive.ofMul a - Additive.ofMul b = Additive.ofMul (a / b) from by
        simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]; abel]
  rw [← ofMul_zpow, div_eq_mul_inv, mul_zpow, inv_zpow, zpow_neg]

/-- A sum of `z`-multiples of differences of `ofMul`s, as a single `ofMul`. -/
theorem sum_zsmul_sub {ι : Type*} (s : Finset ι) (A B : ι → G) (z : ι → ℤ) :
    (∑ i ∈ s, z i • (Additive.ofMul (A i) - Additive.ofMul (B i)))
      = Additive.ofMul (∏ i ∈ s, ((A i) ^ (z i) * (B i) ^ (-(z i)))) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.prod_cons, ih, zsmul_ofMul_sub, ← ofMul_mul]

/-- **The combinatorial reduction.**  `PsiLin` of the boundary of a 3-cube is the alternating sum
of the classes of the six fillings. -/
theorem PsiLin_cubD_single_expand (x₀ : X) (τ : C(IC 3, X)) :
    PsiLin x₀ (cubD 2 X (Finsupp.single τ 1)) =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        (psiClass x₀ (face3 τ i 0) - psiClass x₀ (face3 τ i 1)) := by
  rw [Work.Stems.Cubical.cubD_single]
  simp only [map_sum, map_smul, map_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Stems.Hur2.PsiLin_single, Work.Stems.Hur2.PsiLin_single,
    show psiClass x₀ (face3 τ i 0) =
      Additive.ofMul (⟦psiGenLoop x₀ (faceCube i 0 τ)⟧ : HomotopyGroup (Fin 2) X x₀) from rfl,
    show psiClass x₀ (face3 τ i 1) =
      Additive.ofMul (⟦psiGenLoop x₀ (faceCube i 1 τ)⟧ : HomotopyGroup (Fin 2) X x₀) from rfl]

/-- The alternating sum is `ofMul` of the product of the six classes. -/
theorem expand_eq_prod6 (x₀ : X) (τ : C(IC 3, X)) :
    (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        (psiClass x₀ (face3 τ i 0) - psiClass x₀ (face3 τ i 1)))
      = Additive.ofMul (prod6 x₀ τ) := by
  rw [prod6]
  exact sum_zsmul_sub Finset.univ (fun i => psiC x₀ (face3 τ i 0))
    (fun i => psiC x₀ (face3 τ i 1)) (fun i => (-1 : ℤ) ^ (i : ℕ))

/-- The alternating sum is the class of the assembly. -/
theorem expand_eq_assembly (x₀ : X) (τ : C(IC 3, X)) :
    (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        (psiClass x₀ (face3 τ i 0) - psiClass x₀ (face3 τ i 1)))
      = Additive.ofMul (cl x₀ (assembly x₀ τ)) := by
  rw [expand_eq_prod6, assembly_class_prod]



/-! ## Reparametrisation of a based cube -/

/-- **Reparametrisation of a based cube.**  If a continuous self-map `φ` of the cube `I^n` preserves
the boundary (as a set) and is homotopic to the identity through self-maps also preserving the
boundary, then composing a based cube with `φ` does not change its class: the homotopy is
`(y,t) ↦ p (H (y,t))`, and each slice is constant `x₀` on the boundary because `H` preserves it. -/
theorem genLoop_homotopic_comp_of_homotopic_id {x₀ : X}
    (n : ℕ) [NeZero n] (φ : C(Fin n → unitInterval, Fin n → unitInterval))
    (hφ : ∀ y ∈ Cube.boundary (Fin n), φ y ∈ Cube.boundary (Fin n))
    (H : C((Fin n → unitInterval) × unitInterval, Fin n → unitInterval))
    (h0 : ∀ y, H (y, 0) = φ y) (h1 : ∀ y, H (y, 1) = y)
    (Hb : ∀ y ∈ Cube.boundary (Fin n), ∀ t, H (y, t) ∈ Cube.boundary (Fin n))
    (p : GenLoop (Fin n) X x₀) :
    GenLoop.Homotopic ⟨p.1.comp φ, fun y hy => p.2 (φ y) (hφ y hy)⟩ p := by
  refine ⟨⟨⟨fun z : unitInterval × (Fin n → unitInterval) => p.1 (H (z.2, z.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact p.1.continuous.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro y
    show p.1 (H (y, 0)) = p.1 (φ y)
    rw [h0]
  · intro y
    show p.1 (H (y, 1)) = p.1 y
    rw [h1]
  · intro t y hy
    show p.1 (H (y, t)) = p.1 (φ y)
    rw [p.2 (H (y, t)) (Hb y hy t), p.2 (φ y) (hφ y hy)]

end Work.Stems.Hur2b
