import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# Joins of root groups with the same source are admissible

`Work.EKLContract.IsHoro U` is the frozen contract that a subgroup `U ≤ SL₃(ℝ)` be closed,
normalised by the diagonal group `A = {aDiag t}` and contracted by some `aDiag t`
(`isHoro_Uij.lean` verifies it for the individual root groups `U_ij = {u_ij(s) = 1 + s E_ij}`).

This file verifies it for the join of two root groups with the **same source**,

`U_ij ⊔ U_ik`,  `i ≠ j`, `i ≠ k`,

which is the two-dimensional group of "row `i`" unipotent matrices `1 + s E_ij + t E_ik`.

The mathematics (all of it explicit `3 × 3` matrix bookkeeping on top of `horoUij_*`):

* the two root groups commute: `E_ij E_ik = δ_{j i} E_ik = 0` and `E_ik E_ij = δ_{k i} E_ij = 0`
  because `i ≠ j`, `i ≠ k`; hence `(s,t) ↦ u_ij(s) u_ik(t)` is a homomorphism
  `(ℝ²,+) → SL₃(ℝ)`, and the join is exactly its range (`srcU_sup_eq_sub`);
* such a matrix is `1` outside the two slots `(i,j)`, `(i,k)`, and conversely any element of
  `SL₃(ℝ)` agreeing with `1` outside those slots is a product `u_ij(s) u_ik(t)` — which exhibits
  the join as a finite intersection of closed entry conditions, hence closed
  (`srcU_sub_eq_set`, `srcU_set_closed`);
* `aDiag τ · u_ij(s) u_ik(t) · (aDiag τ)⁻¹ = u_ij(e^{τ_i - τ_j} s) u_ik(e^{τ_i - τ_k} t)`,
  so the diagonal group normalises the join;
* for `t` with `t i = 0`, `t j = t k = 1` (possible exactly when `j ≠ k`) both exponents are
  negative and the conjugates tend to `1` as `n → ∞` (`srcU_contraction`).

The degenerate case `j = k` (the two root groups coincide) is handled by proof irrelevance and
reduces to `isHoro_Uij`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-! ## The parametrisation `(s,t) ↦ u_ij(s)·u_ik(t)` -/

/-- The shape element `u_ij(s) · u_ik(t)`.  It is the general element of `U_ij ⊔ U_ik` when
`j ≠ k`, and `u_ij(s + t)` when `j = k`. -/
def srcU_shape {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (s t : ℝ) : SL3 :=
  uij hij s * uij hik t

/-- The underlying matrix of a shape element: `1 + s E_ij + t E_ik`. -/
lemma srcU_toMat {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (s t : ℝ) :
    toMat (srcU_shape hij hik s t) = 1 + Matrix.single i j s + Matrix.single i k t := by
  unfold srcU_shape
  rw [toMat_mul, horoUij_toMat hij, horoUij_toMat hik]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne (c := s) (i := i) (j := j) (k := i) hij.symm (d := t)]
  abel

/-- The root groups `U_ij` and `U_ik` commute (`i ≠ j`, `i ≠ k`), so `srcU_shape` is
multiplicative in its parameters. -/
lemma srcU_mul {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (s t s' t' : ℝ) :
    srcU_shape hij hik s t * srcU_shape hij hik s' t' =
      srcU_shape hij hik (s + s') (t + t') := by
  apply ext_toMat
  rw [toMat_mul, srcU_toMat, srcU_toMat, srcU_toMat]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne (c := s) (i := i) (j := j) (k := i) hij.symm (d := s'),
    Matrix.single_mul_single_of_ne (c := s) (i := i) (j := j) (k := i) hij.symm (d := t'),
    Matrix.single_mul_single_of_ne (c := t) (i := i) (j := k) (k := i) hik.symm (d := s'),
    Matrix.single_mul_single_of_ne (c := t) (i := i) (j := k) (k := i) hik.symm (d := t'),
    Matrix.single_add, add_zero]
  abel

lemma srcU_shape_zero {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) :
    srcU_shape hij hik 0 0 = (1 : SL3) := by
  simp [srcU_shape, horoUij_zero]

lemma srcU_shape_inv {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (s t : ℝ) :
    (srcU_shape hij hik s t)⁻¹ = srcU_shape hij hik (-s) (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [srcU_mul, show s + -s = (0 : ℝ) from by ring, show t + -t = (0 : ℝ) from by ring,
    srcU_shape_zero]

/-- The subgroup `{u_ij(s) u_ik(t)}`, the range of a homomorphism `(ℝ²,+) → SL₃(ℝ)`. -/
def srcU_sub {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) : Subgroup SL3 where
  carrier := Set.range (fun p : ℝ × ℝ => srcU_shape hij hik p.1 p.2)
  one_mem' := ⟨(0, 0), srcU_shape_zero hij hik⟩
  mul_mem' := by
    rintro x y ⟨⟨s, t⟩, rfl⟩ ⟨⟨s', t'⟩, rfl⟩
    exact ⟨(s + s', t + t'), (srcU_mul hij hik s t s' t').symm⟩
  inv_mem' := by
    rintro x ⟨⟨s, t⟩, rfl⟩
    exact ⟨(-s, -t), (srcU_shape_inv hij hik s t).symm⟩

lemma srcU_mem_sub {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (g : SL3) :
    g ∈ srcU_sub hij hik ↔ ∃ s t : ℝ, srcU_shape hij hik s t = g := by
  constructor
  · rintro ⟨⟨s, t⟩, h⟩; exact ⟨s, t, h⟩
  · rintro ⟨s, t, h⟩; exact ⟨(s, t), h⟩

/-- `U_ij ⊔ U_ik` is exactly the range of `(s,t) ↦ u_ij(s) u_ik(t)`. -/
lemma srcU_sup_eq_sub {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) :
    Uij hij ⊔ Uij hik = srcU_sub hij hik := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · apply (Subgroup.closure_le (srcU_sub hij hik)).mpr
      rintro x ⟨s, rfl⟩
      exact (srcU_mem_sub hij hik _).mpr ⟨s, 0, by simp [srcU_shape, horoUij_zero]⟩
    · apply (Subgroup.closure_le (srcU_sub hij hik)).mpr
      rintro x ⟨t, rfl⟩
      exact (srcU_mem_sub hij hik _).mpr ⟨0, t, by simp [srcU_shape, horoUij_zero]⟩
  · intro x hx
    rw [srcU_mem_sub] at hx
    obtain ⟨s, t, rfl⟩ := hx
    unfold srcU_shape
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨s, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩))

/-! ## Closedness -/

/-- Entries of an element of `SL₃(ℝ)` are continuous functions of the element. -/
lemma srcU_continuous_entry (i j : Fin 3) : Continuous fun g : SL3 => toMat g i j :=
  (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)

/-- The carrier of `U_ij ⊔ U_ik` described by entries: everything agrees with `1` outside the
slots `(i,j)` and `(i,k)`. -/
def srcU_set (i j k : Fin 3) : Set SL3 :=
  {g | ∀ a b : Fin 3, ¬((a = i ∧ b = j) ∨ (a = i ∧ b = k)) →
    toMat g a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b}

lemma srcU_set_closed (i j k : Fin 3) : IsClosed (srcU_set i j k) := by
  have hset : srcU_set i j k =
      ⋂ (p : {p : Fin 3 × Fin 3 // ¬((p.1 = i ∧ p.2 = j) ∨ (p.1 = i ∧ p.2 = k))}),
        {g : SL3 | toMat g p.1.1 p.1.2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1.1 p.1.2} := by
    ext g
    simp only [srcU_set, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
    constructor
    · intro H a h; exact H a.1 a.2 h
    · intro H a b h; exact H (a, b) h
  rw [hset]
  exact isClosed_iInter fun p => isClosed_eq (srcU_continuous_entry p.1.1 p.1.2) continuous_const

/-- Entry `(i,j)` of `1 + s E_ij + t E_ik` with `s = g_{ij}`, `t = g_{ik}`. -/
lemma srcU_entry_ij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (g : SL3) :
    (1 + Matrix.single i j (toMat g i j) + Matrix.single i k (toMat g i k) :
        Matrix (Fin 3) (Fin 3) ℝ) i j = toMat g i j := by
  simp [hij, hjk.symm]

/-- Entry `(i,k)` of `1 + s E_ij + t E_ik` with `s = g_{ij}`, `t = g_{ik}`. -/
lemma srcU_entry_ik {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) (g : SL3) :
    (1 + Matrix.single i j (toMat g i j) + Matrix.single i k (toMat g i k) :
        Matrix (Fin 3) (Fin 3) ℝ) i k = toMat g i k := by
  simp [hik, hjk]

/-- Every other entry of `1 + s E_ij + t E_ik` with `s = g_{ij}`, `t = g_{ik}` is the identity's
entry. -/
lemma srcU_entry_off {i j k : Fin 3} (g : SL3) {a b : Fin 3}
    (hab : ¬((a = i ∧ b = j) ∨ (a = i ∧ b = k))) :
    (1 + Matrix.single i j (toMat g i j) + Matrix.single i k (toMat g i k) :
        Matrix (Fin 3) (Fin 3) ℝ) a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by
  have h1 : (Matrix.single i j (toMat g i j) : Matrix (Fin 3) (Fin 3) ℝ) a b = 0 := by
    rw [Matrix.single_apply]; exact if_neg (fun h => hab (Or.inl ⟨h.1.symm, h.2.symm⟩))
  have h2 : (Matrix.single i k (toMat g i k) : Matrix (Fin 3) (Fin 3) ℝ) a b = 0 := by
    rw [Matrix.single_apply]; exact if_neg (fun h => hab (Or.inr ⟨h.1.symm, h.2.symm⟩))
  simp [Matrix.add_apply, h1, h2]

/-- For `j ≠ k`, the range of `(s,t) ↦ u_ij(s) u_ik(t)` is the set of matrices agreeing with `1`
outside the slots `(i,j)` and `(i,k)`. -/
lemma srcU_sub_eq_set {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((srcU_sub hij hik : Subgroup SL3) : Set SL3) = srcU_set i j k := by
  ext g
  change g ∈ srcU_sub hij hik ↔ g ∈ srcU_set i j k
  rw [srcU_mem_sub]
  constructor
  · rintro ⟨s, t, rfl⟩ a b hab
    rw [srcU_toMat]
    have h1 : (Matrix.single i j s : Matrix (Fin 3) (Fin 3) ℝ) a b = 0 := by
      rw [Matrix.single_apply]; exact if_neg (fun h => hab (Or.inl ⟨h.1.symm, h.2.symm⟩))
    have h2 : (Matrix.single i k t : Matrix (Fin 3) (Fin 3) ℝ) a b = 0 := by
      rw [Matrix.single_apply]; exact if_neg (fun h => hab (Or.inr ⟨h.1.symm, h.2.symm⟩))
    simp [Matrix.add_apply, h1, h2]
  · intro hg
    refine ⟨toMat g i j, toMat g i k, ?_⟩
    apply ext_toMat
    rw [srcU_toMat]
    funext a b
    by_cases hab : (a = i ∧ b = j) ∨ (a = i ∧ b = k)
    · rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb]; exact srcU_entry_ij hij hjk g
      · rw [ha, hb]; exact srcU_entry_ik hik hjk g
    · rw [srcU_entry_off g hab, hg a b hab]

lemma srcU_sub_isClosed {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IsClosed ((srcU_sub hij hik : Subgroup SL3) : Set SL3) := by
  rw [srcU_sub_eq_set hij hik hjk]
  exact srcU_set_closed i j k

/-! ## Normalisation by the diagonal group -/

/-- Conjugation by `aDiag τ` rescales the two slots independently:
`aDiag τ · u_ij(s) u_ik(t) · (aDiag τ)⁻¹ = u_ij(e^{τ_i - τ_j} s) u_ik(e^{τ_i - τ_k} t)`. -/
lemma srcU_aDiag_conj {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (τ : Fin 3 → ℝ)
    (s t : ℝ) :
    aDiag τ * srcU_shape hij hik s t * (aDiag τ)⁻¹ =
      srcU_shape hij hik (Real.exp (τ i - τ j) * s) (Real.exp (τ i - τ k) * t) := by
  unfold srcU_shape
  rw [show aDiag τ * (uij hij s * uij hik t) * (aDiag τ)⁻¹ =
      (aDiag τ * uij hij s * (aDiag τ)⁻¹) * (aDiag τ * uij hik t * (aDiag τ)⁻¹) from by group,
    horoUij_aDiag_conj, horoUij_aDiag_conj]

/-! ## Contraction -/

/-- The exponent vector `(0, 1, 1)` on `(i, j, k)`: contracts both root groups `U_ij`, `U_ik`.
Defined when `j ≠ k` so that `j` and `k` are not confused. -/
def srcU_exp (i j k : Fin 3) : Fin 3 → ℝ :=
  fun c => if c = j then 1 else if c = k then 1 else 0

lemma srcU_exp_i {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) : srcU_exp i j k i = 0 := by
  simp only [srcU_exp]
  rw [if_neg hij, if_neg hik]

lemma srcU_exp_j (i j k : Fin 3) : srcU_exp i j k j = 1 := by
  simp [srcU_exp]

lemma srcU_exp_k {i j k : Fin 3} (hjk : j ≠ k) : srcU_exp i j k k = 1 := by
  simp [srcU_exp, hjk.symm]

lemma srcU_pow_conj {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (τ : Fin 3 → ℝ) (n : ℕ)
    (s t : ℝ) :
    aDiag τ ^ n * srcU_shape hij hik s t * (aDiag τ ^ n)⁻¹ =
      srcU_shape hij hik (Real.exp ((n : ℝ) * (τ i - τ j)) * s)
        (Real.exp ((n : ℝ) * (τ i - τ k)) * t) := by
  rw [horoUij_aDiag_pow τ n, srcU_aDiag_conj]
  congr 2 <;> (congr 1; ring)

/-- `Real.exp (n x) → 0` for `x < 0`. -/
lemma srcU_tendsto_exp {x : ℝ} (hx : x < 0) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * x)) atTop (𝓝 0) := by
  have h1 : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx
  have h0 : 0 ≤ Real.exp x := Real.exp_nonneg x
  have hp : Tendsto (fun n : ℕ => Real.exp x ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  simpa only [Real.exp_nat_mul] using hp

/-- The conjugated diagonal powers of a shape element tend to `1` as `n → ∞`. -/
lemma srcU_contraction {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (s t : ℝ) :
    Tendsto
      (fun n : ℕ => aDiag (srcU_exp i j k) ^ n * srcU_shape hij hik s t *
        (aDiag (srcU_exp i j k) ^ n)⁻¹) atTop (𝓝 1) := by
  have hi : srcU_exp i j k i = 0 := srcU_exp_i hij hik
  have hj : srcU_exp i j k j = 1 := srcU_exp_j i j k
  have hk : srcU_exp i j k k = 1 := srcU_exp_k hjk
  have hx1 : srcU_exp i j k i - srcU_exp i j k j < 0 := by rw [hi, hj]; norm_num
  have hx2 : srcU_exp i j k i - srcU_exp i j k k < 0 := by rw [hi, hk]; norm_num
  have e1 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k j)))
      atTop (𝓝 0) := srcU_tendsto_exp hx1
  have e2 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k k)))
      atTop (𝓝 0) := srcU_tendsto_exp hx2
  have e1' : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k j)) * s)
      atTop (𝓝 0) := by simpa using e1.mul_const s
  have e2' : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k k)) * t)
      atTop (𝓝 0) := by simpa using e2.mul_const t
  have h1 : Tendsto
      (fun n : ℕ => uij hij (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k j)) * s))
      atTop (𝓝 1) := by
    have h1' : Tendsto
        (fun n : ℕ => uij hij (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k j)) * s))
        atTop (𝓝 (uij hij 0)) := ((horoUij_cont hij).tendsto 0).comp e1'
    rw [horoUij_zero hij] at h1'
    exact h1'
  have h2 : Tendsto
      (fun n : ℕ => uij hik (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k k)) * t))
      atTop (𝓝 1) := by
    have h2' : Tendsto
        (fun n : ℕ => uij hik (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k k)) * t))
        atTop (𝓝 (uij hik 0)) := ((horoUij_cont hik).tendsto 0).comp e2'
    rw [horoUij_zero hik] at h2'
    exact h2'
  have hmul := h1.mul h2
  simp only [one_mul] at hmul
  have heq : (fun n : ℕ => aDiag (srcU_exp i j k) ^ n * srcU_shape hij hik s t *
        (aDiag (srcU_exp i j k) ^ n)⁻¹)
      = fun n : ℕ =>
          uij hij (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k j)) * s) *
          uij hik (Real.exp ((n : ℝ) * (srcU_exp i j k i - srcU_exp i j k k)) * t) := by
    funext n
    rw [srcU_pow_conj]
    rfl
  rw [heq]
  exact hmul

/-! ## The non-degenerate case of the target -/

/-- `IsHoro (U_ij ⊔ U_ik)` when `j ≠ k`: closed by `srcU_sub_eq_set`, normalised by
`srcU_aDiag_conj` and contracted by `srcU_exp`. -/
theorem srcU_isHoro_sup {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IsHoro (Uij hij ⊔ Uij hik) := by
  rw [srcU_sup_eq_sub hij hik]
  refine ⟨srcU_sub_isClosed hij hik hjk, ?_, srcU_exp i j k, ?_⟩
  · intro τ u hu
    rw [srcU_mem_sub] at hu ⊢
    obtain ⟨s, t, rfl⟩ := hu
    exact ⟨Real.exp (τ i - τ j) * s, Real.exp (τ i - τ k) * t,
      (srcU_aDiag_conj hij hik τ s t).symm⟩
  · intro u hu
    rw [srcU_mem_sub] at hu
    obtain ⟨s, t, rfl⟩ := hu
    exact srcU_contraction hij hik hjk s t

/-! ## The target -/

theorem isHoro_sup_same_source {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) :
    Work.EKLContract.IsHoro (Work.EKLContract.Uij hij ⊔ Work.EKLContract.Uij hik) := by
  by_cases hjk : j = k
  · subst hjk
    have hU : Uij hij = Uij hik := congrArg Uij (Subsingleton.elim hij hik)
    simpa [hU] using isHoro_Uij hik
  · exact srcU_isHoro_sup hij hik hjk

end Work.EKLContract.Lemmas
