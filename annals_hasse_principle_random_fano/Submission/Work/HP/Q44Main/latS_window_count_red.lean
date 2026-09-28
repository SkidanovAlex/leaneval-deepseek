import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDEstimates.ReducFactor
import Submission.Work.HP.MDEstimates.linFormIntVec
import Submission.Work.HP.MDEstimates.hypLatCount
import Submission.Work.HP.Q44Main.latS_quad_count
import Submission.Work.HP.Q44Main.latS_cub_count
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.prim_lat_window_finite
import Submission.Work.Q44Geom.formOf_eval
-- import Submission.Work.HP.Q44Main.latS_hyper_count
-- import Submission.Work.HP.Q44Main.latS_quad_count
-- import Submission.Work.HP.Q44Main.latS_cub_count

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open MvPolynomial Finset

namespace Work.HP.Q44Main

open Work.HP

/-!
# The window count for reducible quartics (`latS_window_count_red`)

The counting set is
`K = {L : IsPrimLat L ∧ rk L = 3 ∧ (∀ j, lam L (j+1) ≤ s j) ∧ c ∈ vanishOn L}`.

Since `f = formOf 4 4 c` is reducible, it is a product `A · B` of two nonconstant homogeneous
forms of degrees `(1,3)` or `(2,2)`.  Every `L ∈ K` satisfies `f|_L = 0`, and because the
coordinate ring of a `ℚ`-vector space is a domain, one of `A|_L`, `B|_L` vanishes.  Iterating,

* a homogeneous polynomial of degree `1` vanishing on `L` forces `L` into a rank-`4` primitive
  hyperplane: `≪ s₀⁶s₁⁴s₂²` lattices,
* a homogeneous polynomial of degree `2` (resp. `3`) vanishing on `L` either has a linear factor
  (previous case) or is counted by `latS_quad_count` (resp. `latS_cub_count`): `≪ (s₀s₁s₂)³`.
-/

/-! ## Scaling of evaluations of a homogeneous polynomial -/

lemma eval_smul_homogeneous {d : ℕ} {g : MvPolynomial (Fin 5) ℚ} (hg : g.IsHomogeneous d)
    (N : ℚ) (w : Fin 5 → ℚ) :
    MvPolynomial.eval (fun i => N * w i) g = N ^ d * MvPolynomial.eval w g := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmc : g.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hw : (Finsupp.weight (fun _ : Fin 5 => (1 : ℕ))) m = d := hg hmc
  have hsum : (∑ i ∈ m.support, m i) = d := by
    have h := hw
    rw [Finsupp.weight_apply] at h
    simp only [Finsupp.sum, smul_eq_mul, mul_one] at h
    exact h
  have hprod : (∏ i ∈ m.support, (N * w i) ^ m i)
      = N ^ d * ∏ i ∈ m.support, w i ^ m i := by
    have h1 : ∀ i ∈ m.support, (N * w i) ^ m i = N ^ (m i) * w i ^ (m i) := by
      intro i _
      rw [mul_pow]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  rw [hprod]; ring

/-! ## The pullback of a polynomial along a `ℤ`-basis of `L` -/

/-- The `j`-th basis vector of `L`, as a vector of `ℤ^5`. -/
def bv {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    (j : Fin n) : Fin 5 → ℤ := ((b j : ↥L) : Fin 5 → ℤ)

/-- The "generic point": the substitution sending `X_i` to the linear form `Σ_j (bv b j i) X_j`. -/
def genPt {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L) :
    Fin 5 → MvPolynomial (Fin n) ℚ :=
  fun i => ∑ j, MvPolynomial.C ((bv b j i : ℤ) : ℚ) * MvPolynomial.X j

/-- The pullback of `g` along the basis: `g(bv_0 X_0 + bv_1 X_1 + bv_2 X_2)` as a polynomial
in the three coordinates. -/
def zeta {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    (g : MvPolynomial (Fin 5) ℚ) : MvPolynomial (Fin n) ℚ := MvPolynomial.bind₁ (genPt b) g

lemma eval_genPt {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    (y : Fin n → ℚ) (i : Fin 5) :
    MvPolynomial.eval y (genPt b i) = ∑ j, (bv b j i : ℚ) * y j := by
  simp [genPt, MvPolynomial.eval_sum, MvPolynomial.eval_mul]

/-- Evaluating the pullback at `y` is evaluating `g` at the corresponding `ℚ`-linear combination
of the basis vectors. -/
lemma eval_zeta {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    (g : MvPolynomial (Fin 5) ℚ) (y : Fin n → ℚ) :
    MvPolynomial.eval y (zeta b g)
      = MvPolynomial.eval (fun i => ∑ j, (bv b j i : ℚ) * y j) g := by
  have h := MvPolynomial.aeval_bind₁ (R := ℚ) (S := ℚ) (σ := Fin 5) (τ := Fin n) y (genPt b) g
  simp only [MvPolynomial.aeval_eq_eval, zeta, eval_genPt] at h
  exact h

/-- `x ∈ L` equals the linear combination of the basis vectors given by its coordinates. -/
lemma eq_sum_repr {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    (x : Fin 5 → ℤ) (hx : x ∈ L) : x = ∑ j, (b.repr ⟨x, hx⟩ j) • bv b j := by
  have h := b.sum_repr ⟨x, hx⟩
  have h2 := congrArg (Submodule.subtype L) h
  rw [map_sum] at h2
  rw [Finset.sum_congr rfl (fun j _ => map_zsmul (Submodule.subtype L) _ _)] at h2
  simpa [bv] using h2.symm

/-- **Vanishing on the basis implies vanishing of the pullback.** -/
lemma zeta_eq_zero {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    {d : ℕ} {g : MvPolynomial (Fin 5) ℚ} (hg : g.IsHomogeneous d)
    (hvan : ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) g = 0) :
    zeta b g = 0 := by
  refine MvPolynomial.funext_set (fun _ : Fin n => Set.range (fun z : ℤ => (z : ℚ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro y hy
  obtain ⟨m, rfl⟩ : ∃ m : Fin n → ℤ, y = fun i => (m i : ℚ) := by
    choose m hm using fun i => Set.mem_pi.mp hy i (Set.mem_univ i)
    exact ⟨m, funext fun i => (hm i).symm⟩
  have hpt : (fun i => ∑ j, (bv b j i : ℚ) * ((m j : ℤ) : ℚ))
      = fun i => (((∑ j, m j • bv b j : Fin 5 → ℤ) i : ℚ)) := by
    funext i
    rw [Finset.sum_apply, Int.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring
  rw [eval_zeta b g (fun i => ((m i : ℤ) : ℚ)), hpt]
  exact hvan _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)

/-- **Vanishing of the pullback implies vanishing on `L`.** -/
lemma vanish_of_zeta_eq_zero {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)}
    (b : Module.Basis (Fin n) ℤ ↥L) {g : MvPolynomial (Fin 5) ℚ} (h : zeta b g = 0) :
    ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) g = 0 := by
  intro x hx
  have hcoord : (fun i => ∑ j, (bv b j i : ℚ) * ((b.repr ⟨x, hx⟩ j : ℤ) : ℚ))
      = fun i => (x i : ℚ) := by
    funext i
    have hx' := congrFun (eq_sum_repr b x hx) i
    rw [hx', Finset.sum_apply, Int.cast_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring
  rw [← hcoord, ← eval_zeta b g (fun j => ((b.repr ⟨x, hx⟩ j : ℤ) : ℚ)), h]
  simp

/-- **Splitting lemma.**  If a *homogeneous* polynomial `g = l · h` vanishes on the lattice `L`,
then one of the two factors vanishes on `L`. -/
lemma vanish_split {n : ℕ} {L : Submodule ℤ (Fin 5 → ℤ)} (b : Module.Basis (Fin n) ℤ ↥L)
    {d : ℕ} {g l h : MvPolynomial (Fin 5) ℚ} (hg : g.IsHomogeneous d) (hgh : g = l * h)
    (hvan : ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) g = 0) :
    (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) l = 0) ∨
      (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) h = 0) := by
  have hz : zeta b g = 0 := zeta_eq_zero b hg hvan
  have hz' : zeta b l * zeta b h = 0 := by
    have : zeta b (l * h) = zeta b l * zeta b h := map_mul _ _ _
    rw [← this, ← hgh]; exact hz
  rcases mul_eq_zero.mp hz' with h1 | h1
  · exact Or.inl (vanish_of_zeta_eq_zero b h1)
  · exact Or.inr (vanish_of_zeta_eq_zero b h1)

lemma one_le_s (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    ∀ j : Fin 3, 1 ≤ s j := by
  intro j
  fin_cases j
  · exact hs0
  · exact le_trans hs0 hs01
  · exact le_trans (le_trans hs0 hs01) hs12

/-- The window conditions: primitive, rank `3`, successive minima bounded by `s`. -/
def Win (s : Fin 3 → ℝ) (L : Submodule ℤ (Fin 5 → ℤ)) : Prop :=
  IsPrimLat L ∧ rk L = 3 ∧ (∀ j : Fin 3, lam L (j.val + 1) ≤ s j)

lemma Win_finite (s : Fin 3 → ℝ) (hs : ∀ j, 1 ≤ s j) :
    ({L : Submodule ℤ (Fin 5 → ℤ) | Win s L}).Finite :=
  (prim_lat_window_finite (Fin 5) 3 s hs).subset fun L hL => ⟨hL.1, hL.2.1, hL.2.2⟩

/-- The set counted by the theorem. -/
def Kset (c : Mon 4 4 → ℤ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | Win s L ∧ c ∈ vanishOn L}

lemma Kset_finite {c : Mon 4 4 → ℤ} {s : Fin 3 → ℝ} (hs : ∀ j, 1 ≤ s j) :
    (Kset c s).Finite := (Win_finite s hs).subset fun L hL => hL.1

lemma formOf_homog (c : Mon 4 4 → ℤ) : (formOf 4 4 c).IsHomogeneous 4 := by
  rw [Work.Q44Geom.formOf_eq_polyOfR]
  exact Work.Q44Geom.isHomogeneous_polyOfR _

/-- The members of `Kset c s` are lattices on which `formOf 4 4 c` vanishes. -/
lemma Kset_van {c : Mon 4 4 → ℤ} {s : Fin 3 → ℝ} {L : Submodule ℤ (Fin 5 → ℤ)}
    (hL : L ∈ Kset c s) :
    ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) (formOf 4 4 c) = 0 := by
  intro x hx
  have h := (Work.HP.mem_vanishOn (L := L) (a := c)).mp hL.2 ⟨x, hx⟩
  have h2 := Work.Q44Geom.formOf_eval c x
  have key : MvPolynomial.eval (fun i => (x i : ℚ)) (formOf 4 4 c) =
      (formEval (R := ℤ) 4 4 c x : ℚ) := by
    show MvPolynomial.eval (Work.Q44Geom.toRatLM x) (formOf 4 4 c) = _
    exact h2
  rw [key]
  have h' : formEval (R := ℤ) 4 4 c x = 0 := by simpa using h
  exact_mod_cast h' 

lemma exists_basis (L : Submodule ℤ (Fin 5 → ℤ)) :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) ℤ ↥L, True :=
  ⟨(Submodule.basisOfPid (Pi.basisFun ℤ (Fin 5)) L).1,
    (Submodule.basisOfPid (Pi.basisFun ℤ (Fin 5)) L).2, trivial⟩

/-- **Splitting the counting set along a product decomposition.** -/
lemma Kset_split {c : Mon 4 4 → ℤ} {s : Fin 3 → ℝ} {A B : MvPolynomial (Fin 5) ℚ}
    (hAB : formOf 4 4 c = A * B) (hs : ∀ j, 1 ≤ s j) :
    ((Kset c s).ncard : ℝ) ≤
      ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ) +
      ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ) := by
  classical
  have hsub : Kset c s ⊆
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}) ∪
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}) := by
    intro L hL
    obtain ⟨n, b, -⟩ := exists_basis L
    rcases vanish_split b (formOf_homog c) hAB (Kset_van hL) with h | h
    · exact Or.inl ⟨hL, h⟩
    · exact Or.inr ⟨hL, h⟩
  have hfin : (((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}) ∪
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}))).Finite :=
    ((Kset_finite hs).inter_of_left _).union ((Kset_finite hs).inter_of_left _)
  have h := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_union_le (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0})
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0})
  have h3 : ((Kset c s).ncard : ℝ) ≤
      (((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}) ∪
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0})).ncard : ℕ) := by
    exact_mod_cast h
  have h4 : ((((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}) ∪
      (Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0})).ncard : ℕ) : ℝ) ≤
      ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ) +
      ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ) := by
    exact_mod_cast h2
  linarith

/-- A set-theoretic helper: a union bound for `ncard`. -/
lemma ncard_union3_le {α : Type*} (S₁ S₂ S₃ : Set α) :
    ((S₁ ∪ S₂ ∪ S₃).ncard : ℝ) ≤ (S₁.ncard : ℝ) + (S₂.ncard : ℝ) + (S₃.ncard : ℝ) := by
  have h1 : (S₁ ∪ S₂ ∪ S₃).ncard ≤ (S₁ ∪ S₂).ncard + S₃.ncard := Set.ncard_union_le _ _
  have h2 : (S₁ ∪ S₂).ncard ≤ S₁.ncard + S₂.ncard := Set.ncard_union_le _ _
  have h3 : ((S₁ ∪ S₂ ∪ S₃).ncard : ℝ) ≤ ((S₁ ∪ S₂).ncard : ℝ) + (S₃.ncard : ℝ) := by
    exact_mod_cast h1
  have h4 : (((S₁ ∪ S₂).ncard : ℕ) : ℝ) ≤ (S₁.ncard : ℝ) + (S₂.ncard : ℝ) := by
    exact_mod_cast h2
  linarith


/-- The hyperplane-count constant (the "hyp" piece). -/
def HypBound (C : ℝ) : Prop := ∀ (a : Fin 5 → ℤ), a ≠ 0 →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
          (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
          (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * ((s 0) ^ 6 * (s 1) ^ 4 * (s 2) ^ 2)

/-- The quadric-count constant. -/
def QuadBound (C : ℝ) : Prop := ∀ (Q : MvPolynomial (Fin 5) ℚ), Q.IsHomogeneous 2 → Q ≠ 0 →
    (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False) →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
          (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
          (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 0 * s 1 * s 2) ^ 3

/-- The cubic-count constant. -/
def CubBound (C : ℝ) : Prop := ∀ (B : MvPolynomial (Fin 5) ℚ), B.IsHomogeneous 3 → B ≠ 0 →
    (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
          (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
          (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 0 * s 1 * s 2) ^ 3

/-- The hyperplane-count constant for a *linear form*. -/
def LinBound (C : ℝ) : Prop := ∀ (ℓ : MvPolynomial (Fin 5) ℚ), ℓ.IsHomogeneous 1 → ℓ ≠ 0 →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      ∀ (T : Set (Submodule ℤ (Fin 5 → ℤ))),
        T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | Win s L ∧
          ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) ℓ = 0} →
        (T.ncard : ℝ) ≤ C * ((s 0) ^ 6 * (s 1) ^ 4 * (s 2) ^ 2)

-- the three counting pieces, as axioms for development:
/-- The hyperplane count (`MDEstimates.hypLatCount`), restated as `HypBound`. -/
theorem hyp_count_ax : ∃ C : ℝ, 0 < C ∧ HypBound C :=
  Work.HP.MDEstimates.hypLatCount

/-- The quadric count (`Q44Main.latS_quad_count`), restated as `QuadBound`. -/
theorem quad_count_ax : ∃ C : ℝ, 0 < C ∧ QuadBound C :=
  Work.HP.Q44Main.latS_quad_count

/-- The cubic count (`Q44Main.latS_cub_count`), restated as `CubBound`. -/
theorem cub_count_ax : ∃ C : ℝ, 0 < C ∧ CubBound C :=
  Work.HP.Q44Main.latS_cub_count

/-- The hyperplane count for a linear form follows from the "hyp" piece. -/
lemma lin_of_hyp (Ch : ℝ) (h : HypBound Ch) : LinBound Ch := by
  intro ℓ hℓ hℓ0 s hs0 hs01 hs12 T hT
  obtain ⟨a, ha0, ha⟩ := Work.HP.MDEstimates.linFormIntVec ℓ hℓ hℓ0
  have hsub : T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
      (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
      (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)} := by
    intro L hL
    obtain ⟨hwin, hvan⟩ := hT hL
    refine ⟨hwin.1, hwin.2.1, hwin.2.2, fun x hx => ?_⟩
    refine ha x ?_
    have h := hvan x hx
    simpa [Work.Q44Geom.toRatLM] using h
  have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
  have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
      (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
      (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)}).Finite :=
    (Win_finite s hfen).subset fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩
  have h1 : (T.ncard : ℝ) ≤
      (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
      (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
      (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  exact le_trans h1 (h a ha0 s hs0 hs01 hs12)

/-- **The quadratic handler.**  A nonzero homogeneous quadratic either has a linear factor, in
which case the hyperplane count applies twice, or it is covered by the quadric count. -/
lemma quad_bound' (C : ℝ) (hCnn : 0 ≤ C) (hCh : LinBound C) (hCq : QuadBound C)
    (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0) :
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      ∀ (T : Set (Submodule ℤ (Fin 5 → ℤ))),
        T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | Win s L ∧
          ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0} →
        (T.ncard : ℝ) ≤ (3 * C) *
          (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
  classical
  intro s hs0 hs01 hs12 T hT
  by_cases hcase : ∃ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 ∧ ℓ ∣ Q
  · obtain ⟨ℓ, hℓ1, hℓdvd⟩ := hcase
    obtain ⟨h, hh⟩ := hℓdvd
    have hℓ0 : ℓ ≠ 0 := by intro h0; rw [h0, zero_mul] at hh; exact hQ0 hh
    have hh0 : h ≠ 0 := by intro h0; rw [h0, mul_zero] at hh; exact hQ0 hh
    obtain ⟨i, j, hij, hℓi, hhj⟩ :=
      Work.HP.MDEstimates.ReducFactor.isHomogeneous_of_mul_eq hQ hh hℓ0 hh0
    have hi1 : i = 1 := by
      have h1 := hℓ1.totalDegree hℓ0
      have h2 := hℓi.totalDegree hℓ0
      omega
    subst hi1
    have hj1 : j = 1 := by omega
    subst hj1
    set Tℓ : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | Win s L ∧
      ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) ℓ = 0} with hTℓ
    set Th : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | Win s L ∧
      ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) h = 0} with hTh
    have hsub : T ⊆ (T ∩ Tℓ) ∪ (T ∩ Th) := by
      intro L hL
      obtain ⟨n, b, -⟩ := exists_basis L
      rcases vanish_split b hQ hh (hT hL).2 with h1 | h1
      · exact Or.inl ⟨hL, (hT hL).1, h1⟩
      · exact Or.inr ⟨hL, (hT hL).1, h1⟩
    have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
    have hfin : ((T ∩ Tℓ) ∪ (T ∩ Th)).Finite :=
      ((Win_finite s hfen).subset fun L hL => hL.2.1).union
        ((Win_finite s hfen).subset fun L hL => hL.2.1)
    have h1 : ((T ∩ Tℓ).ncard : ℝ) ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) :=
      hCh ℓ hℓ1 hℓ0 s hs0 hs01 hs12 _ fun L hL => hL.2
    have h2 : ((T ∩ Th).ncard : ℝ) ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) :=
      hCh h hhj hh0 s hs0 hs01 hs12 _ fun L hL => hL.2
    have h63 : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have h64 : (0:ℝ) ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have hcast1 : (T.ncard : ℝ) ≤ (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have hcast2 : (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) ≤
        ((T ∩ Tℓ).ncard : ℝ) + ((T ∩ Th).ncard : ℝ) := by
      exact_mod_cast Set.ncard_union_le (T ∩ Tℓ) (T ∩ Th)
    calc (T.ncard : ℝ) ≤ (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) := hcast1
      _ ≤ ((T ∩ Tℓ).ncard : ℝ) + ((T ∩ Th).ncard : ℝ) := hcast2
      _ ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) + C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) :=
          add_le_add h1 h2
      _ ≤ (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [h63, h64, hCnn]
  · push_neg at hcase
    have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
    have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)}).Finite :=
      (Win_finite s hfen).subset fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩
    have hsub : T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)} := by
      intro L hL
      exact ⟨(hT hL).1.1, (hT hL).1.2.1, (hT hL).1.2.2, (hT hL).2⟩
    have hcast : (T.ncard : ℝ) ≤
        (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) Q = 0)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have h64 : (0:ℝ) ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have h63 : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have hC := hCq Q hQ hQ0 hcase s hs0 hs01 hs12
    calc (T.ncard : ℝ) ≤ _ := hcast
      _ ≤ C * (s 0 * s 1 * s 2) ^ 3 := hC
      _ ≤ (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [h63, h64, hCnn]

/-- **The cubic handler.** -/
lemma cub_bound' (C : ℝ) (hCnn : 0 ≤ C) (hCh : LinBound C) (hCq : QuadBound C) (hCc : CubBound C)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0) :
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      ∀ (T : Set (Submodule ℤ (Fin 5 → ℤ))),
        T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | Win s L ∧
          ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0} →
        (T.ncard : ℝ) ≤ (5 * C) *
          (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
  classical
  intro s hs0 hs01 hs12 T hT
  by_cases hcase : ∃ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 ∧ ℓ ∣ B
  · obtain ⟨ℓ, hℓ1, hℓdvd⟩ := hcase
    obtain ⟨h, hh⟩ := hℓdvd
    have hℓ0 : ℓ ≠ 0 := by intro h0; rw [h0, zero_mul] at hh; exact hB0 hh
    have hh0 : h ≠ 0 := by intro h0; rw [h0, mul_zero] at hh; exact hB0 hh
    obtain ⟨i, j, hij, hℓi, hhj⟩ :=
      Work.HP.MDEstimates.ReducFactor.isHomogeneous_of_mul_eq hB hh hℓ0 hh0
    have hi1 : i = 1 := by
      have h1 := hℓ1.totalDegree hℓ0
      have h2 := hℓi.totalDegree hℓ0
      omega
    subst hi1
    have hj2 : j = 2 := by omega
    subst hj2
    set Tℓ : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | Win s L ∧
      ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) ℓ = 0} with hTℓ
    set Th : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | Win s L ∧
      ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) h = 0} with hTh
    have hsub : T ⊆ (T ∩ Tℓ) ∪ (T ∩ Th) := by
      intro L hL
      obtain ⟨n, b, -⟩ := exists_basis L
      rcases vanish_split b hB hh (hT hL).2 with h1 | h1
      · exact Or.inl ⟨hL, (hT hL).1, h1⟩
      · exact Or.inr ⟨hL, (hT hL).1, h1⟩
    have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
    have hfin : ((T ∩ Tℓ) ∪ (T ∩ Th)).Finite :=
      ((Win_finite s hfen).subset fun L hL => hL.2.1).union
        ((Win_finite s hfen).subset fun L hL => hL.2.1)
    have h1 : ((T ∩ Tℓ).ncard : ℝ) ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) :=
      hCh ℓ hℓ1 hℓ0 s hs0 hs01 hs12 _ fun L hL => hL.2
    have h2 : ((T ∩ Th).ncard : ℝ) ≤ (3 * C) *
        (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
      quad_bound' C hCnn hCh hCq h hhj hh0 s hs0 hs01 hs12 _ fun L hL => hL.2
    have h63 : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have h64 : (0:ℝ) ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have hcast1 : (T.ncard : ℝ) ≤ (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have hcast2 : (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) ≤
        ((T ∩ Tℓ).ncard : ℝ) + ((T ∩ Th).ncard : ℝ) := by
      exact_mod_cast Set.ncard_union_le (T ∩ Tℓ) (T ∩ Th)
    calc (T.ncard : ℝ) ≤ (((T ∩ Tℓ) ∪ (T ∩ Th)).ncard : ℝ) := hcast1
      _ ≤ ((T ∩ Tℓ).ncard : ℝ) + ((T ∩ Th).ncard : ℝ) := hcast2
      _ ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) + (3 * C) *
            (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := add_le_add h1 h2
      _ ≤ (5 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [h63, h64, hCnn]
  · push_neg at hcase
    have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
    have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)}).Finite :=
      (Win_finite s hfen).subset fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1⟩
    have hsub : T ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)} := by
      intro L hL
      exact ⟨(hT hL).1.1, (hT hL).1.2.1, (hT hL).1.2.2, (hT hL).2⟩
    have hcast : (T.ncard : ℝ) ≤
        (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have h64 : (0:ℝ) ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have h63 : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    have hC := hCc B hB hB0 hcase s hs0 hs01 hs12
    calc (T.ncard : ℝ) ≤ _ := hcast
      _ ≤ C * (s 0 * s 1 * s 2) ^ 3 := hC
      _ ≤ (5 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [h63, h64, hCnn]

/-- **The window count for reducible quartics.** -/
theorem latS_window_count_red :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Mon 4 4 → ℤ), c ≠ 0 → ¬ Irreducible (formOf 4 4 c) →
      ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
        (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
           (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧ c ∈ vanishOn L} :
          Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
          ≤ C * ((s 0) ^ 6 * (s 1) ^ 4 * (s 2) ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
  obtain ⟨Ch, hChpos, hCh⟩ := hyp_count_ax
  obtain ⟨Cq, hCqpos, hCq⟩ := cub_count_ax
  obtain ⟨Cc, hCcpos, hCc⟩ := quad_count_ax
  set C : ℝ := max (max Ch Cq) Cc with hCdef
  have hChle : Ch ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCqle : Cq ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCcle : Cc ≤ C := le_max_right _ _
  have hCnn : 0 ≤ C := le_trans (le_of_lt hChpos) hChle
  -- transport the three counting bounds to the common constant `C`
  have hHyp : HypBound C := by
    intro a ha s hs0 hs01 hs12
    have h := hCh a ha s hs0 hs01 hs12
    have hX : (0:ℝ) ≤ (s 0) ^ 6 * (s 1) ^ 4 * (s 2) ^ 2 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    exact le_trans h (by nlinarith [hChle, hX])
  have hQuad : QuadBound C := by
    intro Q hQ hQ0 hnol s hs0 hs01 hs12
    have h := hCc Q hQ hQ0 hnol s hs0 hs01 hs12
    have hX : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    exact le_trans h (by nlinarith [hCcle, hX])
  have hCub : CubBound C := by
    intro B hB hB0 hnol s hs0 hs01 hs12
    have h := hCq B hB hB0 hnol s hs0 hs01 hs12
    have hX : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
      have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
      have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
      have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
      positivity
    exact le_trans h (by nlinarith [hCqle, hX])
  have hLin : LinBound C := lin_of_hyp C hHyp
  refine ⟨7 * C, by positivity, ?_⟩
  intro c hc hred s hs0 hs01 hs12
  have hfen : ∀ j : Fin 3, 1 ≤ s j := one_le_s s hs0 hs01 hs12
  have hKset : ({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
      (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧ c ∈ vanishOn L} : Set (Submodule ℤ (Fin 5 → ℤ)))
      = Kset c s := by
    ext L
    simp only [Kset, Win, Set.mem_setOf_eq]
    tauto
  have h63 : (0:ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
    have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
    have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
    positivity
  have h64 : (0:ℝ) ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
    have h1 : 0 < s 0 := lt_of_lt_of_le zero_lt_one hs0
    have h2 : 0 < s 1 := lt_of_lt_of_le zero_lt_one (le_trans hs0 hs01)
    have h3 : 0 < s 2 := lt_of_lt_of_le zero_lt_one (le_trans (le_trans hs0 hs01) hs12)
    positivity
  rw [hKset]
  rcases Work.HP.MDEstimates.ReducFactor.exists_homogeneous_factor c hc hred with
    ⟨A, B, hA1, hB3, hA0, hB0, hAB⟩ | ⟨A, B, hA2, hB2, hA0, hB0, hAB⟩
  · have hsplit := Kset_split hAB hfen
    have hA : ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ)
        ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) :=
      hLin A hA1 hA0 s hs0 hs01 hs12 _ fun L hL => ⟨hL.1.1, hL.2⟩
    have hB : ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ)
        ≤ (5 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
      cub_bound' C hCnn hLin hQuad hCub B hB3 hB0 s hs0 hs01 hs12 _
        fun L hL => ⟨hL.1.1, hL.2⟩
    calc ((Kset c s).ncard : ℝ) ≤
          ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
            ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ) +
          ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
            ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ) :=
          hsplit
      _ ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) +
            (5 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
          add_le_add hA hB
      _ ≤ (7 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [hCnn, h63, h64]
  · have hsplit := Kset_split hAB hfen
    have hA : ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ)
        ≤ (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
      quad_bound' C hCnn hLin hQuad A hA2 hA0 s hs0 hs01 hs12 _
        fun L hL => ⟨hL.1.1, hL.2⟩
    have hB : ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
        ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ)
        ≤ (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
      quad_bound' C hCnn hLin hQuad B hB2 hB0 s hs0 hs01 hs12 _
        fun L hL => ⟨hL.1.1, hL.2⟩
    calc ((Kset c s).ncard : ℝ) ≤
          ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
            ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) A = 0}).ncard : ℝ) +
          ((Kset c s ∩ {L : Submodule ℤ (Fin 5 → ℤ) |
            ∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0}).ncard : ℝ) :=
          hsplit
      _ ≤ (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) +
          (3 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) :=
          add_le_add hA hB
      _ ≤ (7 * C) * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 + (s 0 * s 1 * s 2) ^ 3) := by
          nlinarith [hCnn, h63, h64]

end Work.HP.Q44Main
