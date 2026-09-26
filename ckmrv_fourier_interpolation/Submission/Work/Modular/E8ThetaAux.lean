import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice

/-!
# Foundations for the `E₈` theta series

This file collects the elementary infrastructure needed to compute the theta series of the
`E₈` lattice in the standard model of `Submission.Work.Modular.Lattice`:

* `vec` / `svec` : the integer vectors and the half-integer shift `(1/2, …, 1/2)` in `ℝⁿ`;
* the membership description `E₈ = D₈ ⊔ (D₈ + s)`, where `D₈` is the set of integral vectors
  with even coordinate sum;
* the factorisation of `∑'` over `Fin n → ℤ` into a product of one-dimensional sums;
* summability of the Gaussians occurring in the theta series.
-/

noncomputable section

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

variable {n : ℕ}

/-- The integer vector `m : Fin n → ℤ`, viewed as a point of `ℝⁿ`. -/
noncomputable def vec (m : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (m i : ℝ))

/-- The half-integer shift `(1/2, …, 1/2) ∈ ℝⁿ`. -/
noncomputable def svec : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))

@[simp] lemma vec_ofLp (m : Fin n → ℤ) (i : Fin n) : (vec m).ofLp i = (m i : ℝ) := by
  simp [vec]

@[simp] lemma svec_ofLp (i : Fin n) : (svec : EuclideanSpace ℝ (Fin n)).ofLp i = 1 / 2 := by
  simp [svec]

@[simp] lemma vec_add_svec_ofLp (m : Fin n → ℤ) (i : Fin n) :
    (vec m + svec : EuclideanSpace ℝ (Fin n)).ofLp i = (m i : ℝ) + 1 / 2 := by
  simp

lemma vec_injective : Function.Injective (vec : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n)) := by
  intro m m' h
  funext i
  have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) h
  simp at this
  exact_mod_cast this

lemma vec_add_svec_injective :
    Function.Injective (fun m : Fin n → ℤ => (vec m + svec : EuclideanSpace ℝ (Fin n))) := by
  intro m m' h
  apply vec_injective
  have hh : vec m = vec m' := by
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x - svec) h
    simpa using h2
  exact hh

lemma vec_ne_vec_add_svec [NeZero n] (m m' : Fin n → ℤ) :
    (vec m : EuclideanSpace ℝ (Fin n)) ≠ vec m' + svec := by
  intro h
  have hc := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp 0) h
  simp only [vec_ofLp, vec_add_svec_ofLp] at hc
  have h2 : (2 * (m 0 - m' 0) : ℤ) = 1 := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    linarith
  omega

lemma norm_sq_vec (m : Fin n → ℤ) : ‖vec m‖ ^ 2 = ∑ i, (m i : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

lemma norm_sq_vec_add_svec (m : Fin n → ℤ) :
    ‖(vec m + svec : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, ((m i : ℝ) + 1 / 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

/-! ### The decomposition of `E₈` as `D₈ ⊔ (D₈ + s)` -/

lemma vec_mem_E8 {m : Fin 8 → ℤ} (hm : Even (∑ i, m i)) : vec m ∈ E8 := by
  rw [mem_E8]
  obtain ⟨k, hk⟩ := hm
  have hk2 : ∑ i, m i = 2 * k := by rw [hk]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨2 * m i, by rw [vec_ofLp]; push_cast; ring⟩
  · intro i j
    exact ⟨m i - m j, by rw [vec_ofLp, vec_ofLp]; push_cast; ring⟩
  · refine ⟨k, ?_⟩
    simp only [vec_ofLp]
    have h2 : (∑ i : Fin 8, ((m i : ℤ) : ℝ)) = ((2 * k : ℤ) : ℝ) := by
      rw [← Int.cast_sum, hk2]
    rw [h2]; push_cast; ring

lemma vec_add_svec_mem_E8 {m : Fin 8 → ℤ} (hm : Even (∑ i, m i)) : vec m + svec ∈ E8 := by
  rw [mem_E8]
  obtain ⟨k, hk⟩ := hm
  have hk2 : ∑ i, m i = 2 * k := by rw [hk]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨2 * m i + 1, ?_⟩
    rw [vec_add_svec_ofLp]; push_cast; ring
  · intro i j
    exact ⟨m i - m j, by rw [vec_add_svec_ofLp, vec_add_svec_ofLp]; push_cast; ring⟩
  · refine ⟨k + 2, ?_⟩
    simp only [vec_add_svec_ofLp, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have h2 : (∑ i : Fin 8, ((m i : ℤ) : ℝ)) = ((2 * k : ℤ) : ℝ) := by
      rw [← Int.cast_sum, hk2]
    rw [h2]; push_cast; ring

/-- Membership in `E₈` in terms of integral and half-integral vectors with even coordinate sum. -/
theorem mem_E8_iff_exists {x : EuclideanSpace ℝ (Fin 8)} :
    x ∈ E8 ↔ (∃ m : Fin 8 → ℤ, x = vec m ∧ Even (∑ i, m i)) ∨
             (∃ m : Fin 8 → ℤ, x = vec m + svec ∧ Even (∑ i, m i)) := by
  constructor
  · intro hx
    rw [mem_E8] at hx
    obtain ⟨h2, hd, hs⟩ := hx
    choose u hu using fun i => hd i 0
    obtain ⟨a, ha⟩ := h2 0
    obtain ⟨nc, hn⟩ := hs
    rcases Int.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hx0 : x.ofLp 0 = (c : ℝ) := by
        have hh : (2 : ℝ) * x.ofLp 0 = (2 : ℝ) * (c : ℝ) := by
          rw [ha, hc]; push_cast; ring
        linarith [hh]
      set m : Fin 8 → ℤ := fun i => c + u i with hm
      have hxm : ∀ i, x.ofLp i = (m i : ℝ) := by
        intro i
        have := hu i
        rw [hm]
        push_cast
        linarith [hx0, this]
      refine Or.inl ⟨m, ?_, ?_⟩
      · apply WithLp.ofLp_injective
        funext i
        rw [vec_ofLp]; exact hxm i
      · have hsum1 : ((∑ i, m i : ℤ) : ℝ) = ∑ i, x.ofLp i := by
          rw [Int.cast_sum]
          exact Finset.sum_congr rfl (fun i _ => (hxm i).symm)
        have hEq : (∑ i, m i) = 2 * nc := by
          apply Int.cast_injective (α := ℝ)
          rw [hsum1, hn]; push_cast; ring
        refine ⟨nc, ?_⟩
        rw [hEq]; ring
    · have hx0 : x.ofLp 0 = (c : ℝ) + 1 / 2 := by
        have hh : (2 : ℝ) * x.ofLp 0 = (2 : ℝ) * (c : ℝ) + 1 := by
          rw [ha, hc]; push_cast; ring
        linarith [hh]
      set m : Fin 8 → ℤ := fun i => c + u i with hm
      have hxm : ∀ i, x.ofLp i = (m i : ℝ) + 1 / 2 := by
        intro i
        have := hu i
        rw [hm]
        push_cast
        linarith [hx0, this]
      refine Or.inr ⟨m, ?_, ?_⟩
      · apply WithLp.ofLp_injective
        funext i
        rw [vec_add_svec_ofLp]; exact hxm i
      · have hsum1 : ((∑ i, m i : ℤ) : ℝ) = ∑ i, x.ofLp i - 4 := by
          rw [Int.cast_sum]
          have : ∀ i : Fin 8, ((m i : ℤ) : ℝ) = x.ofLp i - 1 / 2 := by
            intro i; rw [hxm i]; ring
          rw [Finset.sum_congr rfl (fun i _ => this i)]
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
        have hEq : (∑ i, m i) = 2 * nc - 4 := by
          apply Int.cast_injective (α := ℝ)
          rw [hsum1, hn]; push_cast; ring
        refine ⟨nc - 2, ?_⟩
        rw [hEq]; ring
  · rintro (⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩)
    · exact vec_mem_E8 hm
    · exact vec_add_svec_mem_E8 hm

/-- The `D₈` part of `E₈`: integral vectors with even coordinate sum. -/
def D8set : Set (EuclideanSpace ℝ (Fin 8)) :=
  Set.range (fun m : {m : Fin 8 → ℤ // Even (∑ i, m i)} => vec m.1)

/-- The half-integral part of `E₈`. -/
def C8set : Set (EuclideanSpace ℝ (Fin 8)) :=
  Set.range (fun m : {m : Fin 8 → ℤ // Even (∑ i, m i)} => vec m.1 + svec)

lemma mem_D8set {x : EuclideanSpace ℝ (Fin 8)} :
    x ∈ D8set ↔ ∃ m : Fin 8 → ℤ, Even (∑ i, m i) ∧ vec m = x := by
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

lemma mem_C8set {x : EuclideanSpace ℝ (Fin 8)} :
    x ∈ C8set ↔ ∃ m : Fin 8 → ℤ, Even (∑ i, m i) ∧ vec m + svec = x := by
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

lemma vec_mem_D8set {m : Fin 8 → ℤ} : vec m ∈ D8set ↔ Even (∑ i, m i) := by
  rw [mem_D8set]
  constructor
  · rintro ⟨m', hm', h⟩
    exact (vec_injective h) ▸ hm'
  · intro hm; exact ⟨m, hm, rfl⟩

lemma vec_add_svec_mem_C8set {m : Fin 8 → ℤ} :
    vec m + svec ∈ C8set ↔ Even (∑ i, m i) := by
  rw [mem_C8set]
  constructor
  · rintro ⟨m', hm', h⟩
    exact (vec_add_svec_injective h) ▸ hm'
  · intro hm; exact ⟨m, hm, rfl⟩

lemma D8set_subset_E8 : D8set ⊆ (E8 : Set (EuclideanSpace ℝ (Fin 8))) := by
  rintro x ⟨⟨m, hm⟩, rfl⟩
  exact vec_mem_E8 hm

lemma C8set_subset_E8 : C8set ⊆ (E8 : Set (EuclideanSpace ℝ (Fin 8))) := by
  rintro x ⟨⟨m, hm⟩, rfl⟩
  exact vec_add_svec_mem_E8 hm

lemma E8_subset_union : (E8 : Set (EuclideanSpace ℝ (Fin 8))) ⊆ D8set ∪ C8set := by
  intro x hx
  rcases mem_E8_iff_exists.mp hx with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · exact Or.inl ⟨⟨m, hm⟩, rfl⟩
  · exact Or.inr ⟨⟨m, hm⟩, rfl⟩

lemma disjoint_D8set_C8set : Disjoint D8set C8set := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨m, hm⟩, rfl⟩ ⟨⟨m', hm'⟩, h'⟩
  exact vec_ne_vec_add_svec m m' h'.symm

lemma E8_eq_union : (E8 : Set (EuclideanSpace ℝ (Fin 8))) = D8set ∪ C8set :=
  Set.Subset.antisymm E8_subset_union (Set.union_subset D8set_subset_E8 C8set_subset_E8)

/-! ### Factorisation of sums over `Fin n → ℤ` -/

/-- Splitting off the first coordinate of `Fin (n+1) → ι`. -/
noncomputable def piFinSuccEquiv (n : ℕ) (ι : Type*) : (Fin (n+1) → ι) ≃ ι × (Fin n → ι) where
  toFun g := (g 0, Fin.tail g)
  invFun p := Fin.cons p.1 p.2
  left_inv g := Fin.cons_self_tail g
  right_inv p := by ext <;> simp [Fin.cons_zero]

@[simp] lemma piFinSuccEquiv_apply {n : ℕ} {ι : Type*} (g : Fin (n+1) → ι) :
    (piFinSuccEquiv n ι) g = (g 0, Fin.tail g) := rfl
@[simp] lemma piFinSuccEquiv_symm_apply {n : ℕ} {ι : Type*} (p : ι × (Fin n → ι)) :
    (piFinSuccEquiv n ι).symm p = Fin.cons p.1 p.2 := rfl

theorem summable_norm_prod_pi {ι : Type*} (f : ι → ℂ) (hf : Summable fun i => ‖f i‖) :
    ∀ n : ℕ, Summable (fun g : Fin n → ι => ∏ i, ‖f (g i)‖) := by
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hF : Summable (fun p : ι × (Fin n → ι) =>
        (fun a => ‖f a‖) p.1 * (fun h => ∏ i, ‖f (h i)‖) p.2) :=
      summable_mul_of_summable_norm (f := fun a : ι => ‖f a‖)
        (g := fun h : Fin n → ι => ∏ i, ‖f (h i)‖)
        (by simpa using hf) (by simpa using ih)
    have hcomp_eq : (fun g : Fin (n+1) → ι => ∏ i, ‖f (g i)‖)
        = (fun p : ι × (Fin n → ι) => ‖f p.1‖ * ∏ i, ‖f (p.2 i)‖) ∘ (piFinSuccEquiv n ι) := by
      funext g
      rw [Function.comp_apply, piFinSuccEquiv_apply, Fin.prod_univ_succ]
      rfl
    rw [hcomp_eq]
    exact (Equiv.summable_iff (piFinSuccEquiv n ι)).mpr hF

theorem summable_prod_pi {ι : Type*} (f : ι → ℂ) (hf : Summable fun i => ‖f i‖) :
    ∀ n : ℕ, Summable (fun g : Fin n → ι => ∏ i, f (g i)) := by
  intro n
  refine Summable.of_norm_bounded (summable_norm_prod_pi f hf n) (fun g => ?_)
  exact Finset.norm_prod_le Finset.univ (fun i => f (g i))

theorem tsum_prod_pi {ι : Type*} (f : ι → ℂ) (hf : Summable fun i => ‖f i‖) :
    ∀ n : ℕ, (∑' (g : Fin n → ι), ∏ i, f (g i)) = (∑' i, f i)^n := by
  intro n
  induction n with
  | zero => simp [tsum_fintype]
  | succ n ih =>
    have hjoint : Summable (fun p : ι × (Fin n → ι) => f p.1 * ∏ i, f (p.2 i)) := by
      refine Summable.of_norm_bounded
        (g := fun p : ι × (Fin n → ι) => ‖f p.1‖ * ∏ i, ‖f (p.2 i)‖) ?_ (fun p => ?_)
      · exact summable_mul_of_summable_norm (f := fun a : ι => ‖f a‖)
          (g := fun h : Fin n → ι => ∏ i, ‖f (h i)‖) (by simpa using hf)
          (by simpa using summable_norm_prod_pi f hf n)
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (Finset.norm_prod_le Finset.univ (fun i => f (p.2 i))) (norm_nonneg _)
    have hstep : (∑' (g : Fin (n+1) → ι), ∏ i, f (g i))
        = ∑' (p : ι × (Fin n → ι)), f p.1 * ∏ i, f (p.2 i) := by
      rw [← Equiv.tsum_eq (piFinSuccEquiv n ι).symm (fun g : Fin (n+1) → ι => ∏ i, f (g i))]
      apply tsum_congr
      intro p
      simp [Fin.prod_univ_succ]
    rw [hstep, hjoint.tsum_prod]
    simp only [tsum_mul_left, ih]
    rw [tsum_mul_right, pow_succ, mul_comm]

/-! ### Summability of Gaussian sums -/

theorem summable_int_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2)) := by
  have hgeom : Summable (fun n : ℕ => (Real.exp (-c)) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  have hnat : Summable (fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeom
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hn]
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr (fun m => ?_)
  congr 1
  push_cast
  ring

theorem summable_int_exp_neg_mul_sq_shift {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Summable (fun m : ℤ => Real.exp (-c * ((m : ℝ) + d) ^ 2)) := by
  have hbase : Summable (fun m : ℤ => Real.exp (-(c / 2) * (m : ℝ) ^ 2)) :=
    summable_int_exp_neg_mul_sq (by linarith)
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_)
    (hbase.mul_left (Real.exp (c * d ^ 2)))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((m : ℝ) + 2 * d), hc]

end Work.Modular

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-! ### The three Jacobi theta functions and the `E₈` summands -/

/-- `Θ₃ = θ₀₀ = ∑_{m ∈ ℤ} e^{π i m² τ}`. -/
noncomputable def Th3 : ℍ → ℂ := fun τ => jacobiTheta (τ : ℂ)

/-- `Θ₄ = θ₀₁ = ∑_{m ∈ ℤ} (-1)^m e^{π i m² τ}`. -/
noncomputable def Th4 : ℍ → ℂ := fun τ => jacobiTheta₂ (1 / 2) (τ : ℂ)

/-- `Θ₂ = θ₁₀ = ∑_{m ∈ ℤ} e^{π i (m + 1/2)² τ}`. -/
noncomputable def Th2 : ℍ → ℂ := fun τ =>
  Complex.exp (π * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)

/-- The summand `e^{π i τ m²}` of `Θ₃`. -/
noncomputable def phi3 (τ : ℍ) (m : ℤ) : ℂ := Complex.exp (π * Complex.I * (τ : ℂ) * (m : ℂ) ^ 2)

/-- The summand `e^{π i τ (m + 1/2)²}` of `Θ₂`. -/
noncomputable def phi2 (τ : ℍ) (m : ℤ) : ℂ :=
  Complex.exp (π * Complex.I * (τ : ℂ) * ((m : ℂ) + 1 / 2) ^ 2)

/-- The sign `(-1)^m` written as `e^{π i m}`. -/
noncomputable def sgn (m : ℤ) : ℂ := Complex.exp (π * Complex.I * (m : ℂ))

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma thetaTerm_vec (τ : ℍ) (m : Fin 8 → ℤ) :
    thetaTerm τ (vec m) = ∏ i, phi3 τ (m i) := by
  unfold thetaTerm
  rw [norm_sq_vec]
  simp only [phi3]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma thetaTerm_vec_add_svec (τ : ℍ) (m : Fin 8 → ℤ) :
    thetaTerm τ (vec m + svec) = ∏ i, phi2 τ (m i) := by
  unfold thetaTerm
  rw [norm_sq_vec_add_svec]
  simp only [phi2]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

end Work.Modular

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

lemma norm_phi3 (τ : ℍ) (m : ℤ) : ‖phi3 τ m‖ = Real.exp (-π * τ.im * (m:ℝ)^2) := by
  rw [phi3, Complex.norm_exp]
  congr 1
  rw [show π * Complex.I * (τ:ℂ) * (m:ℂ)^2
        = ((π * ((m:ℝ)^2) : ℝ) : ℂ) * (Complex.I * (τ:ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

lemma norm_phi2 (τ : ℍ) (m : ℤ) :
    ‖phi2 τ m‖ = Real.exp (-π * τ.im * ((m:ℝ) + 1/2)^2) := by
  rw [phi2, Complex.norm_exp]
  congr 1
  rw [show π * Complex.I * (τ:ℂ) * ((m:ℂ) + 1/2)^2
        = ((π * (((m:ℝ) + 1/2)^2) : ℝ) : ℂ) * (Complex.I * (τ:ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

lemma summable_norm_phi3 (τ : ℍ) : Summable (fun m : ℤ => ‖phi3 τ m‖) := by
  have hc : 0 < π * τ.im := by have := τ.2; positivity
  simpa only [norm_phi3, neg_mul] using summable_int_exp_neg_mul_sq hc

lemma summable_norm_phi2 (τ : ℍ) : Summable (fun m : ℤ => ‖phi2 τ m‖) := by
  have hc : 0 < π * τ.im := by have := τ.2; positivity
  simpa only [norm_phi2, neg_mul] using summable_int_exp_neg_mul_sq_shift hc (1/2)

lemma sgn_eq_pow (k : ℤ) : sgn k = (-1:ℂ)^k := by
  rw [sgn, show π * Complex.I * (k:ℂ) = (k:ℂ) * (π * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma norm_sgn (m : ℤ) : ‖sgn m‖ = 1 := by
  rw [sgn_eq_pow, norm_zpow, norm_neg, norm_one, one_zpow]

lemma summable_norm_sgn_phi3 (τ : ℍ) : Summable (fun m : ℤ => ‖sgn m * phi3 τ m‖) :=
  (summable_norm_phi3 τ).congr (fun m => by rw [norm_mul, norm_sgn, one_mul])

lemma summable_norm_sgn_phi2 (τ : ℍ) : Summable (fun m : ℤ => ‖sgn m * phi2 τ m‖) :=
  (summable_norm_phi2 τ).congr (fun m => by rw [norm_mul, norm_sgn, one_mul])

lemma prod_sgn {n : ℕ} (m : Fin n → ℤ) : (∏ i, sgn (m i)) = sgn (∑ i, m i) := by
  simp only [sgn]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma sgn_neg_sub_one (m : ℤ) : sgn (-m - 1) = - sgn m := by
  rw [sgn_eq_pow, sgn_eq_pow, neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
  by_cases h : Even m
  · rw [if_pos h, if_neg (by rw [Int.not_even_iff_odd]; exact Even.sub_odd (Even.neg h) odd_one)]
  · rw [if_neg h, if_pos (by
      rw [Int.not_even_iff_odd] at h
      exact Odd.sub_odd (Odd.neg h) odd_one)]
    ring

lemma phi2_neg_sub_one (τ : ℍ) (m : ℤ) : phi2 τ (-m-1) = phi2 τ m := by
  simp only [phi2]
  congr 1
  have : ((↑(-m-1) : ℂ) + 1/2)^2 = ((↑m : ℂ) + 1/2)^2 := by push_cast; ring
  rw [this]

lemma tsum_phi3 (τ : ℍ) : (∑' m : ℤ, phi3 τ m) = Th3 τ := by
  rw [Th3, jacobiTheta]
  apply tsum_congr
  intro m
  rw [phi3]
  congr 1
  ring

lemma tsum_sgn_phi3 (τ : ℍ) : (∑' m : ℤ, sgn m * phi3 τ m) = Th4 τ := by
  rw [Th4, jacobiTheta₂]
  apply tsum_congr
  intro m
  rw [sgn, phi3, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

lemma tsum_phi2 (τ : ℍ) : (∑' m : ℤ, phi2 τ m) = Th2 τ := by
  rw [Th2, jacobiTheta₂]
  simp only [phi2, jacobiTheta₂_term]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [← Complex.exp_add]
  congr 1
  ring

lemma tsum_sgn_phi2 (τ : ℍ) : (∑' m : ℤ, sgn m * phi2 τ m) = 0 := by
  set f : ℤ → ℂ := fun m => sgn m * phi2 τ m with hf
  have hper : ∀ m, f (-m - 1) = -f m := by
    intro m
    simp only [hf, sgn_neg_sub_one, phi2_neg_sub_one, neg_mul]
  let e : ℤ ≃ ℤ := ⟨fun m => -m - 1, fun m => -m - 1, fun m => by ring, fun m => by ring⟩
  have h1 : (∑' m : ℤ, f (e m)) = ∑' m : ℤ, f m := Equiv.tsum_eq e f
  have h2 : (∑' m : ℤ, f (e m)) = ∑' m : ℤ, -f m := tsum_congr (fun m => hper m)
  have h3 : (∑' m : ℤ, -f m) = -(∑' m : ℤ, f m) := tsum_neg
  have hsum : (∑' m : ℤ, f m) = -(∑' m : ℤ, f m) := by
    calc (∑' m : ℤ, f m) = ∑' m : ℤ, f (e m) := h1.symm
      _ = ∑' m : ℤ, -f m := h2
      _ = -(∑' m : ℤ, f m) := h3
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hsum)

end Work.Modular
