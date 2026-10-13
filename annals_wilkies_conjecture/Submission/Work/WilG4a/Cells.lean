/-
  WilG4a — the `n = 1` machinery for BNZ §5.1.

  This module fixes the vocabulary relating a family `F : ℝᵖ → ℝ → ℝ` to the
  `SharpCD`/`SharpDeriv` decomposition of the paper:

  * `famFun F` is the same family read as a single function on `ℝ^{p+1}` (coordinates `(l,x)`);
  * `derivGraphSet F j` is the graph of the `j`-th `x`-derivative of `famFun F` — the set that
    `SharpDeriv` exhibits as an `Ω`-set;
  * `smoothLocus F j` and `derivZeroSet F j` are, respectively, the interior of the `C^j` locus
    and the zero set of the `j`-th derivative inside it;
  * `badLocus F j` is the complement of the `C^j` locus.

  The `Ω`-membership statements are packaged so that the format depends only on the input
  format `F0` (and the dimension), while the degree is a polynomial in the input degree and the
  order `j`.
-/
import Submission.Work.WilG4a.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-! ## Monotonicity of the `Ω` format and degree -/

theorem mono_F_le (S : SOMin) {F D n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n) :
    ∀ {F' : ℕ}, F ≤ F' → X ∈ S.Ω F' D n := fun {F'} hle =>
  Nat.le_induction h (fun _ _ ih => S.mono_F ih) F' hle

theorem mono_D_le (S : SOMin) {F D n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n) :
    ∀ {D' : ℕ}, D ≤ D' → X ∈ S.Ω F D' n := fun {D'} hle =>
  Nat.le_induction h (fun _ _ ih => S.mono_D ih) D' hle

theorem mono_FD_le (S : SOMin) {F F' D D' n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hF : F ≤ F') (hD : D ≤ D') : X ∈ S.Ω F' D' n :=
  mono_D_le S (mono_F_le S h hF) hD

/-! ## The family, read as a function on `ℝ^{p+1}` -/

/-- A family member `F : ℝᵖ → ℝ → ℝ` read as a function `ℝ^{p+1} → ℝ` on `(l,x)`. -/
def famFun {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) : (Fin (p + 1) → ℝ) → ℝ :=
  fun z => f (fun i => z (Fin.castSucc i)) (z (Fin.last p))

@[simp] theorem graphOf_famFun {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) :
    graphOf (famFun f) = graphFam f := rfl

@[simp] theorem famFun_apply {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x : ℝ) :
    famFun f (Fin.snoc l x) = f l x := by
  simp [famFun]

/-- The direction in `Fin (p+1)` in which the derivatives are taken. -/
def xDir (p : ℕ) : Fin (p + 1) := Fin.last p

/-! ## The `Ω`-sets attached to a family member -/

/-- The graph of the `j`-th `x`-derivative of `famFun f` (the set `SharpDeriv` provides). -/
def derivGraphSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {z | Fin.init z ∈ interior {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (famFun f) x} ∧
    z (Fin.last (p + 1)) =
      iteratedFDeriv ℝ j (famFun f) (Fin.init z) (fun _ => Pi.single (xDir p) 1)}

/-- The interior of the `C^j` locus of a family member. -/
def smoothLocus {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  interior {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (famFun f) x}

/-- The complement of the `C^j` locus. -/
def badLocus {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  (smoothLocus f j)ᶜ

/-- The zero set of the `j`-th `x`-derivative of `famFun f`, inside the `C^j` locus. -/
def derivZeroSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  {x | x ∈ smoothLocus f j ∧
    iteratedFDeriv ℝ j (famFun f) x (fun _ => Pi.single (xDir p) 1) = 0}

/-- The fibre of a set in `ℝ^{p+1}` over a parameter `l`. -/
def fibre {p : ℕ} (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) : Set ℝ :=
  {y : ℝ | Fin.snoc l y ∈ Z}

/-! ## `Ω`-membership -/

/-- **The derivative-graph sets are `Ω`-definable** (this is `SharpDeriv` at the direction
`x`).  The format depends only on `F0` and `p`; the degree is `b.eval ![D, j]`. -/
theorem derivGraphSet_mem (S : SOMin) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        derivGraphSet f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2) := by
  obtain ⟨a, b, hb⟩ := hder F0 (p + 1)
  refine ⟨a, b, ?_⟩
  intro D j f hf
  have h := hb D (famFun f) (by rwa [graphOf_famFun]) j (fun _ => xDir p)
  simpa [derivGraphSet, xDir] using h

/-- The interior of the `C^j` locus is `Ω`-definable (projection of the derivative graph). -/
theorem smoothLocus_mem (S : SOMin) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        smoothLocus f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := derivGraphSet_mem S hder p F0
  refine ⟨a + 1, b, ?_⟩
  intro D j f hf
  have hset : projLast (derivGraphSet f j) = smoothLocus f j := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      simp only [derivGraphSet, Set.mem_setOf_eq, Fin.init_snoc] at ht
      exact ht.1
    · intro hx
      refine ⟨iteratedFDeriv ℝ j (famFun f) x (fun _ => Pi.single (xDir p) 1), ?_⟩
      simp only [derivGraphSet, Set.mem_setOf_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hx, trivial⟩
  rw [← hset]
  exact S.proj (hb D j hf)

/-- The complement of the `C^j` locus is `Ω`-definable. -/
theorem badLocus_mem (S : SOMin) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        badLocus f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := smoothLocus_mem S hder p F0
  refine ⟨a + 1, b, ?_⟩
  intro D j f hf
  exact S.compl (hb D j hf)

/-- The zero set of the `j`-th `x`-derivative is `Ω`-definable. -/
theorem derivZeroSet_mem (S : SOMin) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        derivZeroSet f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := derivGraphSet_mem S hder p F0
  refine ⟨a + p + 4, MvPolynomial.X 0 + b + 1, ?_⟩
  intro D j f hf
  have h₁ : derivGraphSet f j ∈ S.Ω (max a (p + 2)) (MvPolynomial.eval ![D, j] b) (p + 2) :=
    mono_F_le S (hb D j hf) (le_max_left _ _)
  have h₂ : {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} ∈
      S.Ω (max a (p + 2)) 1 (p + 2) := by
    have h : {z : Fin (p + 2) → ℝ |
        MvPolynomial.eval z (MvPolynomial.X (Fin.last (p + 1)) :
          MvPolynomial (Fin (p + 2)) ℝ) = 0} ∈ S.Ω (p + 2) 1 (p + 2) := by
      have h0 := S.hyp (p + 2) (MvPolynomial.X (Fin.last (p + 1)) :
        MvPolynomial (Fin (p + 2)) ℝ)
      rwa [MvPolynomial.totalDegree_X] at h0
    have h' : {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} ∈ S.Ω (p + 2) 1 (p + 2) := by
      convert h using 1
      ext z
      simp
    exact mono_F_le S h' (le_max_right _ _)
  have h₃ : (⋂ i : Fin 2, (if i = 0 then derivGraphSet f j
      else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})) ∈
      S.Ω (max a (p + 2) + 1)
        (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![D, j] b else 1)) (p + 2) :=
    S.inter (fun i : Fin 2 => if i = 0 then MvPolynomial.eval ![D, j] b else 1)
      (fun i : Fin 2 => if i = 0 then derivGraphSet f j
        else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})
      (by intro i; fin_cases i <;> simp [h₁, h₂])
  have h₄ := S.proj h₃
  have hsplit : (⋂ i : Fin 2, (if i = 0 then derivGraphSet f j
      else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})) =
      derivGraphSet f j ∩ {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} := by
    ext z
    simp [Fin.forall_fin_two]
  have hset : projLast (derivGraphSet f j ∩ {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0}) =
      derivZeroSet f j := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      rw [Set.mem_inter_iff] at ht
      obtain ⟨hg, h0⟩ := ht
      simp only [derivGraphSet, Set.mem_setOf_eq, Fin.init_snoc, Fin.snoc_last] at hg h0
      refine ⟨?_, ?_⟩
      · change x ∈ interior {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (famFun f) x}
        exact hg.1
      · rw [← hg.2, h0]
    · intro hx
      simp only [derivZeroSet, Set.mem_setOf_eq] at hx
      refine ⟨0, ?_⟩
      rw [Set.mem_inter_iff]
      refine ⟨?_, by simp⟩
      simp only [derivGraphSet, Set.mem_setOf_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hx.1, hx.2.symm⟩
  rw [hsplit] at h₄
  rw [hset] at h₄
  refine mono_FD_le S h₄ ?_ ?_
  · rcases le_total a (p + 2) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  · have hsum : (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![D, j] b else 1)) =
        MvPolynomial.eval ![D, j] b + 1 := by
      rw [Fin.sum_univ_two]
      simp
    have hval : MvPolynomial.eval ![D, j]
        (MvPolynomial.X 0 + b + 1 : MvPolynomial (Fin 2) ℕ) =
        D + MvPolynomial.eval ![D, j] b + 1 := by
      rw [map_add, map_add, MvPolynomial.eval_X, map_one]
      simp
    rw [hsum, hval]
    exact Nat.le_add_left _ _

end Work.WilG4a
