import Mathlib
import Submission.Work.L2F.Defs

/-!
# Four-subgroups are self-centralizing in `PGL(2,F)`

This file proves `Work.L2F.PGL.centralizer_fourGroup`.

The mathematical content: let `F` be a field of odd characteristic and `V ≤ PGL(2,F) = GL(2,F)/Z`
a Klein four-group.  Then `C_{PGL(2,F)}(V) = V`.

The proof is the `2 × 2` linear algebra argument of the docstring below.  Its skeleton:

* lift two distinct non-identity elements of `V` to `A, B ∈ GL(2,F)`.  Then `A² = λ•1`, `B² = μ•1`
  and `(A*B)² = ν•1` with `λ, μ, ν ≠ 0`, and `A`, `B`, `A*B` are not scalar;
* `A`, `B`, `A*B` are traceless (`trace_eq_zero_of_sq_eq_smul_one`), hence anticommute
  (`anticommute_of_traces`), and `{1, A, B, A*B}` is a basis of `M₂(F)`
  (`linearIndependent_aux`, `span_aux`, packaged as `fourGroupBasis`);
* if `x = π(g)` centralizes `V` then `g*A = σ•(A*g)`, `g*B = τ•(B*g)` with `σ² = τ² = 1`
  (`exists_sign_sq_eq_one`); expanding `g` in the basis and matching coefficients in
  `g*A - σ•(A*g) = 0`, `g*B - τ•(B*g) = 0` forces `g ∈ F·{1, A, B, A*B}`
  (`eq_smul_gen_of_sign`), so `π(g) ∈ V`.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PGL

/-- A subgroup of cardinality `4` has two distinct nonidentity elements. -/
lemma fourGroup_two_nonidentity_aux {G : Type*} [Group G] (V : Subgroup G)
    (hV : Nat.card V = 4) : ∃ u w : V, u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  haveI : Fintype V := Fintype.ofFinite V
  have hcard : ((Finset.univ : Finset V).erase 1).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : V)), Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, hV]
  have h2 : 1 < ((Finset.univ : Finset V).erase 1).card := by omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp h2
  exact ⟨u, w, (Finset.mem_erase.mp hu).1, (Finset.mem_erase.mp hw).1, huw⟩

/-! ## Scalar / projective helpers -/

lemma mk_eq_mk_of_eq_smul {F : Type*} [Field F] {X g : Matrix.GeneralLinearGroup (Fin 2) F}
    {c : F} (hc : c ≠ 0)
    (h : (g : Matrix (Fin 2) (Fin 2) F) = c • (X : Matrix (Fin 2) (Fin 2) F)) :
    Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk X := by
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = c := ⟨Units.mk0 c hc, rfl⟩
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix.GeneralLinearGroup (Fin 2) F)
      : Matrix (Fin 2) (Fin 2) F) = (u : F) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hg : g = Matrix.GeneralLinearGroup.scalar (Fin 2) u * X := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, hsc, h, Matrix.smul_mul, one_mul]
  rw [hg, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

lemma ne_zero_of_eq_smul_mk {F : Type*} [Field F] {c : F}
    {X g : Matrix.GeneralLinearGroup (Fin 2) F}
    (h : (g : Matrix (Fin 2) (Fin 2) F) = c • (X : Matrix (Fin 2) (Fin 2) F)) : c ≠ 0 := by
  intro h0
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, h, h0, zero_smul, Matrix.det_zero]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero hdet

lemma not_scalar_of_mk_ne_one {F : Type*} [Field F] {A : Matrix.GeneralLinearGroup (Fin 2) F}
    (h : Matrix.ProjGenLinGroup.mk A ≠ 1) :
    ¬ ∃ c : F, (A : Matrix (Fin 2) (Fin 2) F) = c • 1 := by
  rintro ⟨c, hc⟩
  apply h
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨c, by rw [hc]; ext i j; by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]⟩

/-! ## Traces and the matrix algebra lemmas -/

lemma trace_eq_zero_of_sq_eq_smul_one {F : Type*} [Field F] {X : Matrix (Fin 2) (Fin 2) F}
    {lam : F} (h : X * X = lam • 1) (hns : ¬ ∃ c : F, X = c • 1) : X.trace = 0 := by
  have hCH : X * X = X.trace • X - X.det • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring
  rw [h] at hCH
  by_contra htr
  apply hns
  refine ⟨X.trace⁻¹ * (lam + X.det), ?_⟩
  have h2 : X.trace • X = (lam + X.det) • 1 := by
    rw [eq_comm] at hCH
    rw [sub_eq_iff_eq_add] at hCH
    rw [hCH, ← add_smul]
  have h3 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => X.trace⁻¹ • M) h2
  simp only [smul_smul] at h3
  rw [inv_mul_cancel₀ htr, one_smul] at h3
  exact h3

lemma mul_add_mul_eq_trace_smul_one {F : Type*} [Field F] {X Y : Matrix (Fin 2) (Fin 2) F}
    (hX : X.trace = 0) (hY : Y.trace = 0) :
    X * Y + Y * X = (X * Y).trace • 1 := by
  have hX' : X 1 1 = - X 0 0 := by
    have h := hX; rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  have hY' : Y 1 1 = - Y 0 0 := by
    have h := hY; rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.trace_fin_two, Fin.sum_univ_two,
      Matrix.smul_apply, hX', hY'] <;>
    ring

lemma smul_add_smul_one_eq_zero {F : Type*} [Field F] {A : Matrix (Fin 2) (Fin 2) F} {α β : F}
    (hns : ¬ ∃ c : F, A = c • 1) (h : α • A + β • 1 = 0) : α = 0 ∧ β = 0 := by
  by_cases hα : α = 0
  · subst hα
    simp only [zero_smul, zero_add] at h
    refine ⟨rfl, ?_⟩
    have := congrFun (congrFun h 0) 0
    simpa using this
  · exfalso
    apply hns
    have h2 : A + (α⁻¹ * β) • 1 = 0 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => α⁻¹ • M) h
      simp only [smul_add, smul_smul, smul_zero] at hh
      rw [inv_mul_cancel₀ hα, one_smul] at hh
      exact hh
    exact ⟨-(α⁻¹ * β), by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h2⟩

lemma anticommute_of_traces {F : Type*} [Field F] {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : A.trace = 0) (hB : B.trace = 0) (hAB : (A * B).trace = 0) :
    A * B = -(B * A) := by
  have h := mul_add_mul_eq_trace_smul_one hA hB
  rw [hAB, zero_smul] at h
  exact add_eq_zero_iff_eq_neg.mp h

lemma linearIndependent_aux {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    {A B : Matrix (Fin 2) (Fin 2) F} {lam mu : F}
    (hA : A * A = lam • 1) (hlam : lam ≠ 0)
    (hB : B * B = mu • 1) (hmu : mu ≠ 0)
    (htrA : A.trace = 0) (htrB : B.trace = 0) (htrAB : (A * B).trace = 0)
    (hAns : ¬ ∃ c : F, A = c • 1) :
    ∀ a b c d : F, a • 1 + b • A + c • B + d • (A * B) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro a b c d habcd
  have hBinv : B * ((mu⁻¹) • B) = 1 := by
    rw [Matrix.mul_smul, hB, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  have ha : a = 0 := by
    have h1 : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • A + c • B + d • (A * B)).trace = 0 := by
      rw [habcd]; simp
    have h2 : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • A + c • B + d • (A * B)).trace
        = 2 * a := by
      rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
        Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, htrA, htrB, htrAB,
        Matrix.trace_one, Fintype.card_fin]
      ring
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hchar
    · exact h
  subst ha
  have hbcd : b • A + c • B + d • (A * B) = 0 := by simpa using habcd
  have hb : b = 0 := by
    have hmul : A * (b • A + c • B + d • (A * B))
        = b • (lam • 1) + c • (A * B) + d • (lam • B) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, hA, ← Matrix.mul_assoc, smul_mul,
        Matrix.one_mul]
    have h1 : (b • (lam • 1) + c • (A * B) + d • (lam • B)).trace = 0 := by
      have hzero : b • (lam • 1) + c • (A * B) + d • (lam • B) = 0 := by
        rw [← hmul, hbcd, Matrix.mul_zero]
      rw [hzero]
      simp
    have h2 : (b • (lam • 1) + c • (A * B) + d • (lam • B)).trace = 2 * (b * lam) := by
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htrAB, htrB,
        Fintype.card_fin]
      ring
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hchar
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlam
  subst hb
  have hcd : c • B + d • (A * B) = 0 := by simpa using hbcd
  have hcd' : c • (1 : Matrix (Fin 2) (Fin 2) F) + d • A = 0 := by
    have h3 : (c • (1 : Matrix (Fin 2) (Fin 2) F) + d • A) * B = 0 := by
      rw [Matrix.add_mul, smul_mul, smul_mul, Matrix.one_mul]
      exact hcd
    have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M * ((mu⁻¹) • B)) h3
    rw [Matrix.zero_mul, Matrix.mul_assoc, hBinv, Matrix.mul_one] at h4
    exact h4
  have hfin := smul_add_smul_one_eq_zero hAns (by rw [add_comm]; exact hcd')
  exact ⟨rfl, rfl, hfin.2, hfin.1⟩

lemma span_aux {F : Type*} [Field F] {A B : Matrix (Fin 2) (Fin 2) F}
    (hind : ∀ a b c d : F, a • 1 + b • A + c • B + d • (A * B) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    ∀ X : Matrix (Fin 2) (Fin 2) F, ∃ a b c d : F,
      X = a • 1 + b • A + c • B + d • (A * B) := by
  let b : Fin 4 → Matrix (Fin 2) (Fin 2) F := ![1, A, B, A * B]
  have hLI : LinearIndependent F b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : g 0 • (1 : Matrix (Fin 2) (Fin 2) F) + g 1 • A + g 2 • B + g 3 • (A * B) = 0 := by
      rw [Fin.sum_univ_four] at hg
      simpa [b] using hg
    obtain ⟨h0, h1, h2, h3⟩ := hind (g 0) (g 1) (g 2) (g 3) hsum
    intro i
    fin_cases i <;> assumption
  have htop : Submodule.span F (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hLI, Fintype.card_fin, Module.finrank_matrix]
    simp [Module.finrank_self]
  intro X
  have hX : X ∈ Submodule.span F (Set.range b) := by rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hX
  obtain ⟨c, hc⟩ := hX
  refine ⟨c 0, c 1, c 2, c 3, ?_⟩
  rw [← hc, Fin.sum_univ_four]
  simp [b]

theorem fourGroupBasis (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) F) (lam mu nu : F)
    (hA : A * A = lam • 1) (hlam : lam ≠ 0)
    (hB : B * B = mu • 1) (hmu : mu ≠ 0)
    (hABsq : (A * B) * (A * B) = nu • 1) (hnu : nu ≠ 0)
    (hAns : ¬ ∃ c : F, A = c • 1) (hBns : ¬ ∃ c : F, B = c • 1)
    (hABns : ¬ ∃ c : F, A * B = c • 1) :
    (A * B = -(B * A)) ∧
    (∀ a b c d : F, a • 1 + b • A + c • B + d • (A * B) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∧
    (∀ X : Matrix (Fin 2) (Fin 2) F, ∃ a b c d : F,
      X = a • 1 + b • A + c • B + d • (A * B)) := by
  have htrA : A.trace = 0 := trace_eq_zero_of_sq_eq_smul_one hA hAns
  have htrB : B.trace = 0 := trace_eq_zero_of_sq_eq_smul_one hB hBns
  have htrAB : (A * B).trace = 0 := trace_eq_zero_of_sq_eq_smul_one hABsq hABns
  exact ⟨anticommute_of_traces htrA htrB htrAB,
    linearIndependent_aux h2 hA hlam hB hmu htrA htrB htrAB hAns,
    span_aux (linearIndependent_aux h2 hA hlam hB hmu htrA htrB htrAB hAns)⟩

/-! ## The coefficient chase -/

lemma one_add_one_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) : (1 : F) + 1 ≠ 0 := by
  have h : (1 : F) + 1 = 2 := by norm_num
  rw [h]; exact h2

lemma eq_zero_of_two_mul {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x : F}
    (h : (2 : F) * x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' h2
  · exact h'

lemma eq_zero_of_add_one_mul {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x : F}
    (h : ((1 : F) + 1) * x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (one_add_one_ne_zero h2)
  · exact h'

lemma eq_zero_of_sub_neg_one_mul {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x : F}
    (h : ((1 : F) - -1) * x = 0) : x = 0 := by
  rw [show (1 : F) - -1 = 2 from by norm_num] at h
  exact eq_zero_of_two_mul h2 h

lemma eq_zero_of_neg_add_one_mul {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {x : F}
    (h : -(((1 : F) + 1) * x) = 0) : x = 0 :=
  eq_zero_of_add_one_mul h2 (neg_eq_zero.mp h)

theorem eq_smul_gen_of_sign (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (A B g : Matrix (Fin 2) (Fin 2) F) (lam mu sigma tau : F)
    (hA : A * A = lam • 1) (hlam : lam ≠ 0)
    (hB : B * B = mu • 1) (hmu : mu ≠ 0)
    (hAB : A * B = -(B * A))
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) F, ∃ a b c d : F,
      X = a • 1 + b • A + c • B + d • (A * B))
    (hind : ∀ a b c d : F, a • 1 + b • A + c • B + d • (A * B) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)
    (hsigma : sigma = 1 ∨ sigma = -1) (htau : tau = 1 ∨ tau = -1)
    (hgA : g * A = sigma • (A * g)) (hgB : g * B = tau • (B * g)) :
    (∃ c : F, g = c • (1 : Matrix (Fin 2) (Fin 2) F)) ∨
    (∃ c : F, g = c • A) ∨ (∃ c : F, g = c • B) ∨ (∃ c : F, g = c • (A * B)) := by
  obtain ⟨p, q, r, s, hg⟩ := hspan g
  have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
  have hABA : (A * B) * A = -(lam • B) := by
    rw [Matrix.mul_assoc, hBA, Matrix.mul_neg, ← Matrix.mul_assoc, hA, smul_mul,
      Matrix.one_mul]
  have hABB : (A * B) * B = mu • A := by
    rw [Matrix.mul_assoc, hB, Matrix.mul_smul, Matrix.mul_one]
  have hBAB : B * (A * B) = -(mu • A) := by
    rw [← Matrix.mul_assoc, hBA, Matrix.neg_mul, hABB]
  have hgA_exp : g * A = p • A + (q * lam) • 1 - r • (A * B) - (s * lam) • B := by
    rw [hg]
    simp only [Matrix.add_mul, smul_mul, Matrix.one_mul, hA, hBA, hABA, smul_neg, smul_smul]
    module
  have hAg_exp : A * g = p • A + (q * lam) • 1 + r • (A * B) + (s * lam) • B := by
    rw [hg]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hA, ← Matrix.mul_assoc,
      smul_mul, Matrix.one_mul, smul_smul]
  have hgB_exp : g * B = p • B + (r * mu) • 1 + q • (A * B) + (s * mu) • A := by
    rw [hg]
    simp only [Matrix.add_mul, smul_mul, Matrix.one_mul, hB, hABB, smul_smul]
    module
  have hBg_exp : B * g = p • B + (r * mu) • 1 - q • (A * B) - (s * mu) • A := by
    rw [hg]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hB, hBA, hBAB, smul_neg,
      smul_smul]
    module
  have hzeroA : g * A - sigma • (A * g) = 0 := by rw [hgA, sub_self]
  have hzeroB : g * B - tau • (B * g) = 0 := by rw [hgB, sub_self]
  have hexpA : g * A - sigma • (A * g)
      = ((1 - sigma) * (q * lam)) • (1 : Matrix (Fin 2) (Fin 2) F) + ((1 - sigma) * p) • A
        + (-((1 + sigma) * (s * lam))) • B + (-((1 + sigma) * r)) • (A * B) := by
    rw [hgA_exp, hAg_exp]
    module
  have hexpB : g * B - tau • (B * g)
      = ((1 - tau) * (r * mu)) • (1 : Matrix (Fin 2) (Fin 2) F) + ((1 + tau) * (s * mu)) • A
        + ((1 - tau) * p) • B + ((1 + tau) * q) • (A * B) := by
    rw [hgB_exp, hBg_exp]
    module
  have hcoefA := hind ((1 - sigma) * (q * lam)) ((1 - sigma) * p) (-((1 + sigma) * (s * lam)))
      (-((1 + sigma) * r)) (by rw [← hexpA]; exact hzeroA)
  have hcoefB := hind ((1 - tau) * (r * mu)) ((1 + tau) * (s * mu)) ((1 - tau) * p)
      ((1 + tau) * q) (by rw [← hexpB]; exact hzeroB)
  rcases hsigma with hsig | hsig <;> rcases htau with htau' | htau'
  · obtain ⟨-, -, hsa, hra⟩ := hcoefA
    obtain ⟨-, -, -, hqb⟩ := hcoefB
    have hr : r = 0 := eq_zero_of_neg_add_one_mul h2 (by rw [hsig] at hra; exact hra)
    have hs : s = 0 := by
      have h := eq_zero_of_neg_add_one_mul h2 (by rw [hsig] at hsa; exact hsa)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlam
    have hq : q = 0 := eq_zero_of_add_one_mul h2 (by rw [htau'] at hqb; exact hqb)
    exact Or.inl ⟨p, by rw [hg, hr, hs, hq]; simp⟩
  · obtain ⟨-, -, hsa, hra⟩ := hcoefA
    obtain ⟨-, -, hpb, -⟩ := hcoefB
    have hr : r = 0 := eq_zero_of_neg_add_one_mul h2 (by rw [hsig] at hra; exact hra)
    have hs : s = 0 := by
      have h := eq_zero_of_neg_add_one_mul h2 (by rw [hsig] at hsa; exact hsa)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlam
    have hp : p = 0 := eq_zero_of_sub_neg_one_mul h2 (by rw [htau'] at hpb; exact hpb)
    exact Or.inr (Or.inl ⟨q, by rw [hg, hr, hs, hp]; simp⟩)
  · obtain ⟨hqa, hpa, -, -⟩ := hcoefA
    obtain ⟨-, hsb, -, -⟩ := hcoefB
    have hp : p = 0 := eq_zero_of_sub_neg_one_mul h2 (by rw [hsig] at hpa; exact hpa)
    have hq : q = 0 := by
      have h := eq_zero_of_sub_neg_one_mul h2 (by rw [hsig] at hqa; exact hqa)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlam
    have hs : s = 0 := by
      have h := eq_zero_of_add_one_mul h2 (by rw [htau'] at hsb; exact hsb)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hmu
    exact Or.inr (Or.inr (Or.inl ⟨r, by rw [hg, hp, hq, hs]; simp⟩))
  · obtain ⟨hqa, hpa, -, -⟩ := hcoefA
    obtain ⟨hrb, -, -, -⟩ := hcoefB
    have hp : p = 0 := eq_zero_of_sub_neg_one_mul h2 (by rw [hsig] at hpa; exact hpa)
    have hq : q = 0 := by
      have h := eq_zero_of_sub_neg_one_mul h2 (by rw [hsig] at hqa; exact hqa)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hlam
    have hr : r = 0 := by
      have h := eq_zero_of_sub_neg_one_mul h2 (by rw [htau'] at hrb; exact hrb)
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hmu
    exact Or.inr (Or.inr (Or.inr ⟨s, by rw [hg, hp, hq, hr]; simp⟩))

/-! ## The sign lemma -/

lemma exists_sign_sq_eq_one (F : Type*) [Field F]
    (A g : Matrix.GeneralLinearGroup (Fin 2) F) (w : Fˣ)
    (hA2 : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = (w : F) • 1)
    (h : Matrix.ProjGenLinGroup.mk (A * g) = Matrix.ProjGenLinGroup.mk (g * A)) :
    ∃ σ : F, σ ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
        = σ • ((A : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := by
  obtain ⟨u, hu⟩ := (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mp h
  have hmat : (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
      = (u : F) • ((A : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := by
    have h2 := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h2
    rw [show (Matrix.scalar (Fin 2) (u : F) : Matrix (Fin 2) (Fin 2) F) = (u : F) • 1 from by
          ext i j; by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij],
        Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2.symm
  refine ⟨(u : F), ?_, hmat⟩
  have hdg : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have hh : (((Matrix.GeneralLinearGroup.det g : Fˣ)) : F) ≠ 0 :=
      (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at hh
  have hdA : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have hh : (((Matrix.GeneralLinearGroup.det A : Fˣ)) : F) ≠ 0 :=
      (Matrix.GeneralLinearGroup.det A).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at hh
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hdet
  have hprod : (g : Matrix (Fin 2) (Fin 2) F).det * (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    mul_ne_zero hdg hdA
  have h1 : (u : F) ^ 2 * ((g : Matrix (Fin 2) (Fin 2) F).det
        * (A : Matrix (Fin 2) (Fin 2) F).det)
      = 1 * ((g : Matrix (Fin 2) (Fin 2) F).det * (A : Matrix (Fin 2) (Fin 2) F).det) := by
    rw [mul_comm ((A : Matrix (Fin 2) (Fin 2) F).det) ((g : Matrix (Fin 2) (Fin 2) F).det)] at hdet
    rw [one_mul]
    exact hdet.symm
  exact mul_right_cancel₀ hprod h1

theorem centralizer_fourGroup (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (V : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hV : Work.L2F.IsFourGroup V) :
    Subgroup.centralizer (V : Set (Matrix.ProjGenLinGroup (Fin 2) F)) = V := by
  obtain ⟨hcard, hsq⟩ := hV
  have hVle : V ≤ Subgroup.centralizer (V : Set (Matrix.ProjGenLinGroup (Fin 2) F)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hv2 : v * v = 1 := by simpa [pow_two] using hsq v hv
    have hw2 : w * w = 1 := by simpa [pow_two] using hsq w hw
    have h1 : (v * w) * (v * w) = 1 := by simpa [pow_two] using hsq (v * w) (V.mul_mem hv hw)
    have h3 : w * v = (v * w)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hw2]
    rw [h3, inv_eq_of_mul_eq_one_left h1]
  refine le_antisymm ?_ hVle
  intro x hx
  obtain ⟨a, b, ha1, hb1, hab⟩ := fourGroup_two_nonidentity_aux V hcard
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (a : Matrix.ProjGenLinGroup (Fin 2) F)
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective (b : Matrix.ProjGenLinGroup (Fin 2) F)
  obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  have hab1 : (a * b : V) ≠ 1 := by
    intro h
    have hb2 : b * b = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hsq (b : Matrix.ProjGenLinGroup (Fin 2) F) b.2
    have h1 : (a * b) * b = 1 * b := by rw [h]
    rw [mul_assoc, hb2, mul_one, one_mul] at h1
    exact hab h1
  have hA_ne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    rw [hA]; intro h; exact ha1 (Subtype.ext h)
  have hB_ne : Matrix.ProjGenLinGroup.mk B ≠ 1 := by
    rw [hB]; intro h; exact hb1 (Subtype.ext h)
  have hAB_ne : Matrix.ProjGenLinGroup.mk (A * B) ≠ 1 := by
    rw [map_mul, hA, hB]; intro h; exact hab1 (Subtype.ext h)
  have hA2' : Matrix.ProjGenLinGroup.mk (A * A) = 1 := by
    simp only [map_mul, hA]
    simpa [pow_two] using hsq (a : Matrix.ProjGenLinGroup (Fin 2) F) a.2
  have hB2' : Matrix.ProjGenLinGroup.mk (B * B) = 1 := by
    simp only [map_mul, hB]
    simpa [pow_two] using hsq (b : Matrix.ProjGenLinGroup (Fin 2) F) b.2
  have hAB2' : Matrix.ProjGenLinGroup.mk ((A * B) * (A * B)) = 1 := by
    simp only [map_mul, hA, hB]
    simpa [pow_two] using hsq ((a : Matrix.ProjGenLinGroup (Fin 2) F)
      * (b : Matrix.ProjGenLinGroup (Fin 2) F)) (V.mul_mem a.2 b.2)
  obtain ⟨wA, hwA⟩ : ∃ w : Fˣ, A * A = Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    have hmem : A * A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hA2'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw.symm⟩
  obtain ⟨wB, hwB⟩ : ∃ w : Fˣ, B * B = Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    have hmem : B * B ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hB2'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw.symm⟩
  obtain ⟨wAB, hwAB⟩ : ∃ w : Fˣ, (A * B) * (A * B)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    have hmem : (A * B) * (A * B) ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hAB2'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hmem
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw.symm⟩
  have hA2m : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
      = (wA : F) • 1 := by
    have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hwA
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hB2m : (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)
      = (wB : F) • 1 := by
    have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hwB
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hAB2m : ((A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F))
      * ((A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) = (wAB : F) • 1 := by
    have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hwAB
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hAns := not_scalar_of_mk_ne_one hA_ne
  have hBns := not_scalar_of_mk_ne_one hB_ne
  have hABns := not_scalar_of_mk_ne_one hAB_ne
  obtain ⟨hABanti, hind, hspan⟩ := fourGroupBasis F h2 (A : Matrix (Fin 2) (Fin 2) F)
    (B : Matrix (Fin 2) (Fin 2) F) (wA : F) (wB : F) (wAB : F) hA2m wA.ne_zero hB2m
    wB.ne_zero hAB2m wAB.ne_zero hAns hBns hABns
  have hcommA : Matrix.ProjGenLinGroup.mk (A * g) = Matrix.ProjGenLinGroup.mk (g * A) := by
    simp only [map_mul, hA, hg]
    exact Subgroup.mem_centralizer_iff.mp hx (a : Matrix.ProjGenLinGroup (Fin 2) F) a.2
  have hcommB : Matrix.ProjGenLinGroup.mk (B * g) = Matrix.ProjGenLinGroup.mk (g * B) := by
    simp only [map_mul, hB, hg]
    exact Subgroup.mem_centralizer_iff.mp hx (b : Matrix.ProjGenLinGroup (Fin 2) F) b.2
  obtain ⟨sigma, hsig2, hgArel⟩ := exists_sign_sq_eq_one F A g wA hA2m hcommA
  obtain ⟨tau, htau2, hgBrel⟩ := exists_sign_sq_eq_one F B g wB hB2m hcommB
  have hsig : sigma = 1 ∨ sigma = -1 := by
    have h : (sigma - 1) * (sigma + 1) = 0 := by
      have hh : (sigma - 1) * (sigma + 1) = sigma ^ 2 - 1 := by ring
      rw [hh, hsig2]; ring
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h')
  have htau : tau = 1 ∨ tau = -1 := by
    have h : (tau - 1) * (tau + 1) = 0 := by
      have hh : (tau - 1) * (tau + 1) = tau ^ 2 - 1 := by ring
      rw [hh, htau2]; ring
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h')
  have hmain := eq_smul_gen_of_sign F h2 (A : Matrix (Fin 2) (Fin 2) F)
    (B : Matrix (Fin 2) (Fin 2) F) (g : Matrix (Fin 2) (Fin 2) F) (wA : F) (wB : F) sigma tau
    hA2m wA.ne_zero hB2m wB.ne_zero hABanti hspan hind hsig htau hgArel hgBrel
  rw [← hg]
  rcases hmain with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · have hm : Matrix.ProjGenLinGroup.mk g = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨c, by rw [hc]; ext i j; by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]⟩
    rw [hm]; exact V.one_mem
  · have hm : Matrix.ProjGenLinGroup.mk g = (a : Matrix.ProjGenLinGroup (Fin 2) F) := by
      rw [← hA]
      exact mk_eq_mk_of_eq_smul (ne_zero_of_eq_smul_mk hc) hc
    rw [hm]; exact a.2
  · have hm : Matrix.ProjGenLinGroup.mk g = (b : Matrix.ProjGenLinGroup (Fin 2) F) := by
      rw [← hB]
      exact mk_eq_mk_of_eq_smul (ne_zero_of_eq_smul_mk hc) hc
    rw [hm]; exact b.2
  · have hc' : (g : Matrix (Fin 2) (Fin 2) F)
        = c • ((A * B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      simpa only [Matrix.GeneralLinearGroup.coe_mul] using hc
    have hm : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (A * B) :=
      mk_eq_mk_of_eq_smul (ne_zero_of_eq_smul_mk hc') hc'
    rw [hm]
    simp only [map_mul, hA, hB]
    exact V.mul_mem a.2 b.2

end Work.L2F.PGL
