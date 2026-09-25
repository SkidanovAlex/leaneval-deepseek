import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.sl3_gap_defs
import Submission.Work.LT.sl3_bounded_generation
import Submission.Work.LT.sl3_gap_relT

/-! # `sl3_gap`: uniform spectral gap of `Cay(SL₃(ℤ/p), {E_ij(±1)})`

Route (Shalom's scheme; see `Submission/Work/LT/DESIGN.md` and the guidance in this file):

* `sl3_gap_relT` (delegated, module `Submission.Work.LT.sl3_gap_relT`): relative property (T)
  for the column subgroup `U = {E_ac(s)E_bc(t)} ≅ (ℤ/p)²`, i.e. the `U`-Dirichlet form is
  bounded by the 12-generator Dirichlet form `D`, uniformly in the odd prime `p`.
* From it, using the averaging identity `∑_{u∈U} ‖L_u f - f‖² = 2|U| ‖f - P_U f‖²`, every
  elementary transvection `E_ij(t)` (arbitrary `t`!) satisfies
  `∑_g (f (E_ij(t) g) - f g)² ≤ 2K·D(f)`.
* `sl3_bounded_generation` (sibling): every `g ∈ SL₃(ℤ/p)` is a product of at most `L`
  elementary transvections; telescoping along such a word (with Cauchy–Schwarz over the `L`
  steps, `sg_list_telescope_bound`) bounds `∑_g (f (g h) - f h)²` by `L²·2K·D(f)`.
* Averaging over the finite group `G`: for mean-zero `f`,
  `∑_{h,g} (f (h g) - f g)² = 2|G| ∑ f²`, whence `c = 1/(K·L²)` works.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.LT


open Finset

variable {p : ℕ}

/-! ## 1. Elementary transvection arithmetic -/

private lemma sg_sl3E_zero (i j : Fin 3) (h : i ≠ j) : sl3E p i j 0 = 1 := by
  apply Subtype.ext
  simp only [sl3E, dite_eq_right h, Matrix.SpecialLinearGroup.coe_one, Subtype.coe_mk]
  exact Matrix.transvection_zero i j

private lemma sg_sl3E_mul_same (i j : Fin 3) (h : i ≠ j) (s t : ZMod p) :
    sl3E p i j s * sl3E p i j t = sl3E p i j (s + t) := by
  apply Subtype.ext
  simp only [sl3E, dite_eq_right h, Matrix.SpecialLinearGroup.coe_mul, Subtype.coe_mk]
  exact Matrix.transvection_mul_transvection_same i j h s t

private lemma sg_sl3E_comm (a b c : Fin 3) (hac : a ≠ c) (hbc : b ≠ c) (s t : ZMod p) :
    sl3E p a c s * sl3E p b c t = sl3E p b c t * sl3E p a c s := by
  apply Subtype.ext
  simp only [sl3E, dite_eq_right hac, dite_eq_right hbc, Matrix.SpecialLinearGroup.coe_mul,
    Subtype.coe_mk]
  simp only [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, one_mul, mul_one,
    Matrix.single_mul_single_of_ne s a c b hbc.symm t,
    Matrix.single_mul_single_of_ne t b c a hac.symm s]
  abel

private lemma sg_sl3E_col_mul {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c)
    (s t s' t' : ZMod p) :
    (sl3E p a c s * sl3E p b c t) * (sl3E p a c s' * sl3E p b c t')
      = sl3E p a c (s + s') * sl3E p b c (t + t') := by
  apply Subtype.ext
  simp only [sl3E, dite_eq_right hac, dite_eq_right hbc, Matrix.SpecialLinearGroup.coe_mul,
    Subtype.coe_mk]
  simp only [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, mul_zero,
    zero_mul,
    Matrix.single_mul_single_of_ne s a c b hbc.symm t,
    Matrix.single_mul_single_of_ne s a c a hac.symm s',
    Matrix.single_mul_single_of_ne s a c b hbc.symm t',
    Matrix.single_mul_single_of_ne t b c a hac.symm s,
    Matrix.single_mul_single_of_ne t b c a hac.symm s',
    Matrix.single_mul_single_of_ne t b c b hbc.symm t',
    Matrix.single_mul_single_of_ne t' b c a hac.symm s,
    Matrix.single_mul_single_of_ne t' b c a hac.symm s',
    Matrix.single_mul_single_of_ne s' a c a hac.symm s,
    Matrix.single_mul_single_of_ne s' a c b hbc.symm t,
    Matrix.single_mul_single_of_ne s' a c a hac.symm s',
    Matrix.single_mul_single_of_ne s' a c b hbc.symm t',
    Matrix.single_mul_single_of_ne s a c a hac.symm s,
    Matrix.single_mul_single_of_ne s a c b hbc.symm t,
    Matrix.single_add]
  abel

/-! ## 2. Averaging over a `(ℤ/p)²`-indexed family -/

section Averaging

variable {G : Type*} [Group G] [Fintype G]
variable {q : ℕ} [Fact q.Prime]

/-- `S g = ∑_{s,t} f (u s t * g)`: the (unnormalised) average of `f` along the family `u`. -/
private noncomputable def sg_grpSum (u : ZMod q → ZMod q → G) (f : G → ℝ) (g : G) : ℝ :=
  ∑ s : ZMod q, ∑ t : ZMod q, f (u s t * g)

/-- Reindexing: `∑_g F (a * g) = ∑_g F g`. -/
private lemma sg_sum_mulLeft (a : G) (F : G → ℝ) : ∑ g, F (a * g) = ∑ g, F g := by
  refine Fintype.sum_equiv (Equiv.mulLeft a) (fun g => F (a * g)) F ?_
  intro g; rw [Equiv.coe_mulLeft]

/-- Reindexing: `∑_g F (g * a) = ∑_g F g`. -/
private lemma sg_sum_mulRight (a : G) (F : G → ℝ) : ∑ g, F (g * a) = ∑ g, F g := by
  refine Fintype.sum_equiv (Equiv.mulRight a) (fun g => F (g * a)) F ?_
  intro g; rw [Equiv.coe_mulRight]

/-- `∑_{s,t} c = q² c`. -/
private lemma sg_sum_zmod_const (c : ℝ) : (∑ _s : ZMod q, ∑ _t : ZMod q, c) = (q : ℝ) ^ 2 * c := by
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

private lemma sg_grpSum_invariant {u : ZMod q → ZMod q → G}
    (hu : ∀ s t s' t' : ZMod q, u s t * u s' t' = u (s + s') (t + t'))
    (f : G → ℝ) (s₀ t₀ : ZMod q) (g : G) :
    sg_grpSum u f (u s₀ t₀ * g) = sg_grpSum u f g := by
  unfold sg_grpSum
  have h1 : ∀ s t : ZMod q, f (u s t * (u s₀ t₀ * g)) = f (u (s + s₀) (t + t₀) * g) := by
    intro s t
    rw [← mul_assoc, hu s t s₀ t₀]
  simp only [h1]
  calc ∑ s : ZMod q, ∑ t : ZMod q, f (u (s + s₀) (t + t₀) * g)
      = ∑ s : ZMod q, ∑ t : ZMod q, f (u (s + s₀) t * g) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        exact Fintype.sum_equiv (Equiv.addRight t₀)
          (fun t : ZMod q => f (u (s + s₀) (t + t₀) * g))
          (fun t : ZMod q => f (u (s + s₀) t * g)) (fun t => rfl)
    _ = ∑ s : ZMod q, ∑ t : ZMod q, f (u s t * g) := by
        exact Fintype.sum_equiv (Equiv.addRight s₀)
          (fun s : ZMod q => ∑ t : ZMod q, f (u (s + s₀) t * g))
          (fun s : ZMod q => ∑ t : ZMod q, f (u s t * g)) (fun s => rfl)

private lemma sg_grpSum_sq {u : ZMod q → ZMod q → G}
    (hu : ∀ s t s' t' : ZMod q, u s t * u s' t' = u (s + s') (t + t')) (f : G → ℝ) :
    ∑ g, sg_grpSum u f g ^ 2 = (q : ℝ) ^ 2 * ∑ g, sg_grpSum u f g * f g := by
  have hinv : ∀ (g : G) (s t : ZMod q), sg_grpSum u f (u s t * g) = sg_grpSum u f g :=
    fun g s t => sg_grpSum_invariant hu f s t g
  have hinv' : ∀ (s t : ZMod q) (g : G), sg_grpSum u f ((u s t)⁻¹ * g) = sg_grpSum u f g := by
    intro s t g
    have h := hinv ((u s t)⁻¹ * g) s t
    rw [mul_inv_cancel_left] at h
    exact h.symm
  calc ∑ g, sg_grpSum u f g ^ 2
      = ∑ g, sg_grpSum u f g * (∑ s : ZMod q, ∑ t : ZMod q, f (u s t * g)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [pow_two, sg_grpSum]
    _ = ∑ s : ZMod q, ∑ t : ZMod q, ∑ g, sg_grpSum u f g * f (u s t * g) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ s : ZMod q, ∑ t : ZMod q, ∑ g, sg_grpSum u f g * f g := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        have h1 : (∑ g, sg_grpSum u f g * f (u s t * g))
            = ∑ g, sg_grpSum u f ((u s t)⁻¹ * g) * f g := by
          exact Fintype.sum_equiv (Equiv.mulLeft (u s t))
            (fun g : G => sg_grpSum u f g * f (u s t * g))
            (fun g : G => sg_grpSum u f ((u s t)⁻¹ * g) * f g)
            (fun g => by simp only [Equiv.coe_mulLeft, inv_mul_cancel_left])
        rw [h1]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hinv' s t g]
    _ = (q : ℝ) ^ 2 * ∑ g, sg_grpSum u f g * f g := by
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        ring

/-- Rotating a triple sum. -/
private lemma sg_sum_rotate3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] {M : Type*}
    [AddCommMonoid M] (F : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [h1]
  exact Finset.sum_comm

/-- Splitting a three-term sum. -/
private lemma sg_sum_split3 {ι : Type*} [Fintype ι] (X Y Z : ι → ℝ) :
    (∑ i, (X i - Y i + Z i)) = (∑ i, X i) - (∑ i, Y i) + (∑ i, Z i) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The Dirichlet form of the family `u`, expressed through the average `sg_grpSum`. -/
private lemma sg_dirichlet_eq {u : ZMod q → ZMod q → G}
    (hu : ∀ s t s' t' : ZMod q, u s t * u s' t' = u (s + s') (t + t')) (f : G → ℝ) :
    (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, (f (u s t * g) - f g) ^ 2)
      = 2 * (q : ℝ) ^ 2 * (∑ g, f g ^ 2) - 2 * ∑ g, f g * sg_grpSum u f g := by
  have hterm : ∀ (s t : ZMod q) (g : G),
      (f (u s t * g) - f g) ^ 2 = f (u s t * g) ^ 2 - 2 * (f (u s t * g) * f g) + f g ^ 2 :=
    fun s t g => by ring
  have hA : (∑ s, ∑ t, ∑ g, f (u s t * g) ^ 2) = (q : ℝ) ^ 2 * (∑ g, f g ^ 2) := by
    have h : ∀ s t : ZMod q, (∑ g, f (u s t * g) ^ 2) = ∑ g, f g ^ 2 :=
      fun s t => sg_sum_mulLeft (u s t) (fun g => f g ^ 2)
    simp only [h]
    exact sg_sum_zmod_const _
  have hC : (∑ _s : ZMod q, ∑ _t : ZMod q, ∑ g, f g ^ 2) = (q : ℝ) ^ 2 * (∑ g, f g ^ 2) :=
    sg_sum_zmod_const _
  have hB : (∑ s, ∑ t, ∑ g, 2 * (f (u s t * g) * f g)) = 2 * ∑ g, f g * sg_grpSum u f g := by
    have e1 : (∑ s, ∑ t, ∑ g, 2 * (f (u s t * g) * f g))
        = 2 * ∑ s, ∑ t, ∑ g, f (u s t * g) * f g := by
      simp only [Finset.mul_sum]
    rw [e1, sg_sum_rotate3 (fun s t g => f (u s t * g) * f g)]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [sg_grpSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hsplit : (∑ s : ZMod q, ∑ t : ZMod q,
          ∑ g, (f (u s t * g) ^ 2 - 2 * (f (u s t * g) * f g) + f g ^ 2))
      = (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, f (u s t * g) ^ 2)
        - (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, 2 * (f (u s t * g) * f g))
        + (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, f g ^ 2) := by
    simp only [sg_sum_split3]
  calc (∑ s, ∑ t, ∑ g, (f (u s t * g) - f g) ^ 2)
      = ∑ s, ∑ t, ∑ g, (f (u s t * g) ^ 2 - 2 * (f (u s t * g) * f g) + f g ^ 2) := by
        simp only [hterm]
    _ = (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, f (u s t * g) ^ 2)
          - (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, 2 * (f (u s t * g) * f g))
          + (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, f g ^ 2) := hsplit
    _ = 2 * (q : ℝ) ^ 2 * (∑ g, f g ^ 2) - 2 * ∑ g, f g * sg_grpSum u f g := by
        rw [hA, hB, hC]; ring

/-- Expansion of the squared deviation from the average. -/
private lemma sg_avg_decomp {u : ZMod q → ZMod q → G}
    (hu : ∀ s t s' t' : ZMod q, u s t * u s' t' = u (s + s') (t + t')) (f : G → ℝ) :
    (∑ g, (f g - (1 / (q : ℝ) ^ 2) * sg_grpSum u f g) ^ 2)
      = (∑ g, f g ^ 2) - (1 / (q : ℝ) ^ 2) * ∑ g, f g * sg_grpSum u f g := by
  have hq : (q : ℝ) ≠ 0 := by
    have : (0 : ℕ) < q := (Fact.out : q.Prime).pos
    exact_mod_cast this.ne'
  have hterm : ∀ g : G, (f g - (1 / (q : ℝ) ^ 2) * sg_grpSum u f g) ^ 2
      = f g ^ 2 - 2 * ((1 / (q : ℝ) ^ 2) * (f g * sg_grpSum u f g))
        + (1 / (q : ℝ) ^ 2) ^ 2 * (sg_grpSum u f g) ^ 2 := fun g => by ring
  have hsq := sg_grpSum_sq hu f
  have hX : (∑ g, sg_grpSum u f g * f g) = ∑ g, f g * sg_grpSum u f g :=
    Finset.sum_congr rfl fun g _ => by ring
  have hq2 : (1 / (q : ℝ) ^ 2) ^ 2 * (q : ℝ) ^ 2 = 1 / (q : ℝ) ^ 2 := by
    field_simp
  rw [hX] at hsq
  calc (∑ g, (f g - (1 / (q : ℝ) ^ 2) * sg_grpSum u f g) ^ 2)
      = ∑ g, (f g ^ 2 - 2 * ((1 / (q : ℝ) ^ 2) * (f g * sg_grpSum u f g))
          + (1 / (q : ℝ) ^ 2) ^ 2 * (sg_grpSum u f g) ^ 2) := by simp only [hterm]
    _ = (∑ g, f g ^ 2) - 2 * ((1 / (q : ℝ) ^ 2) * ∑ g, f g * sg_grpSum u f g)
          + (1 / (q : ℝ) ^ 2) ^ 2 * (∑ g, sg_grpSum u f g ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ g, f g ^ 2) - (1 / (q : ℝ) ^ 2) * ∑ g, f g * sg_grpSum u f g := by
        have hstep : (1 / (q : ℝ) ^ 2) ^ 2 * ((q : ℝ) ^ 2 * ∑ g, f g * sg_grpSum u f g)
            = (1 / (q : ℝ) ^ 2) * ∑ g, f g * sg_grpSum u f g := by
          rw [← mul_assoc, hq2]
        rw [hsq, hstep]; ring

end Averaging

/-! ## 3. Per-transvection bound -/


/-- `(a-b)^2 ≤ 2(a²+b²)`. -/
private lemma sg_sq_sub_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

/-! ## 3. From the column bound to single transvections -/

section Column

variable {q : ℕ} [Fact q.Prime]

/-- The column family `u(s,t) = E_ac(s)E_bc(t)`. -/
private def sg_colU {a b c : Fin 3} (s t : ZMod q) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod q) :=
  sl3E q a c s * sl3E q b c t

private lemma sg_colU_mul {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ s t s' t' : ZMod q, sg_colU (q := q) (a := a) (b := b) (c := c) s t
        * sg_colU (q := q) (a := a) (b := b) (c := c) s' t'
      = sg_colU (q := q) (a := a) (b := b) (c := c) (s + s') (t + t') :=
  fun s t s' t' => sg_sl3E_col_mul hac hbc s t s' t'

/-- The `U`-sum is twice `q²` times the squared deviation from the `U`-average. -/
private lemma sg_colsum_eq_dev {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod q) → ℝ) :
    (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, (f (sg_colU (q := q) (a := a) (b := b) (c := c) s t * g) - f g) ^ 2)
      = 2 * (q : ℝ) ^ 2 * ∑ g, (f g - (1 / (q : ℝ) ^ 2)
          * sg_grpSum (fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) f g) ^ 2 := by
  have hu := sg_colU_mul (q := q) (a := a) (b := b) (c := c) hac hbc
  have h1 := sg_dirichlet_eq (u := fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) hu f
  have h2 := sg_avg_decomp (u := fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) hu f
  rw [h1, h2]
  have hq : (q : ℝ) ≠ 0 := by
    have : (0 : ℕ) < q := (Fact.out : q.Prime).pos
    exact_mod_cast this.ne'
  first | (field_simp; ring) | field_simp

/-- A single transvection of the column moves `f` at most `2·‖f - avg‖` in `ℓ²`. -/
private lemma sg_dev_single_le {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod q) → ℝ) (s t : ZMod q) :
    (∑ g, (f (sg_colU (q := q) (a := a) (b := b) (c := c) s t * g) - f g) ^ 2)
      ≤ 4 * ∑ g, (f g - (1 / (q : ℝ) ^ 2)
          * sg_grpSum (fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) f g) ^ 2 := by
  have hu := sg_colU_mul (q := q) (a := a) (b := b) (c := c) hac hbc
  set u : ZMod q → ZMod q → Matrix.SpecialLinearGroup (Fin 3) (ZMod q) :=
    fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t with hu_def
  set S := sg_grpSum u f with hS
  have hinv : ∀ g, S (u s t * g) = S g := fun g => sg_grpSum_invariant (u := u) hu f s t g
  have hpt : ∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod q),
      (f (u s t * g) - f g) ^ 2
        ≤ 2 * ((f (u s t * g) - (1 / (q : ℝ) ^ 2) * S g) ^ 2
            + (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2) := by
    intro g
    have h0 : S (u s t * g) = S g := hinv g
    have h1 : (f (u s t * g) - (1 / (q : ℝ) ^ 2) * S (u s t * g))
        - (f g - (1 / (q : ℝ) ^ 2) * S g) = f (u s t * g) - f g := by
      rw [h0]; ring
    rw [← h1, h0]
    exact sg_sq_sub_le _ _
  have hre : (∑ g, (f (u s t * g) - (1 / (q : ℝ) ^ 2) * S g) ^ 2)
      = ∑ g, (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.mulLeft (u s t))
      (fun g => (f (u s t * g) - (1 / (q : ℝ) ^ 2) * S g) ^ 2)
      (fun g => (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2) ?_
    intro g
    simp only [Equiv.coe_mulLeft]
    rw [hinv g]
  calc (∑ g, (f (u s t * g) - f g) ^ 2)
      ≤ ∑ g, 2 * ((f (u s t * g) - (1 / (q : ℝ) ^ 2) * S g) ^ 2
            + (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2) :=
        Finset.sum_le_sum fun g _ => hpt g
    _ = 2 * ((∑ g, (f (u s t * g) - (1 / (q : ℝ) ^ 2) * S g) ^ 2)
            + (∑ g, (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_add_distrib
    _ = 2 * ((∑ g, (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2)
            + (∑ g, (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2)) := by rw [hre]
    _ = 4 * ∑ g, (f g - (1 / (q : ℝ) ^ 2) * S g) ^ 2 := by ring

/-- **Per-transvection bound** from the column bound. -/
private lemma sg_col_bound_single {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c)
    {f : Matrix.SpecialLinearGroup (Fin 3) (ZMod q) → ℝ} {K D : ℝ}
    (hcol : (∑ s : ZMod q, ∑ t : ZMod q, ∑ g,
        (f (sg_colU (q := q) (a := a) (b := b) (c := c) s t * g) - f g) ^ 2)
      ≤ K * (q : ℝ) ^ 2 * D)
    (s t : ZMod q) :
    (∑ g, (f (sg_colU (q := q) (a := a) (b := b) (c := c) s t * g) - f g) ^ 2)
      ≤ 2 * K * D := by
  have h1 := sg_colsum_eq_dev (q := q) (a := a) (b := b) (c := c) hac hbc f
  have h2 := sg_dev_single_le (q := q) (a := a) (b := b) (c := c) hac hbc f s t
  have hq : (0 : ℝ) < (q : ℝ) ^ 2 := by
    have hpos : (0 : ℕ) < q := (Fact.out : q.Prime).pos
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hpos
    positivity
  have hdev : (∑ g, (f g - (1 / (q : ℝ) ^ 2)
      * sg_grpSum (fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) f g) ^ 2)
      ≤ K * D / 2 := by
    have h4 : 2 * (q : ℝ) ^ 2 * (∑ g, (f g - (1 / (q : ℝ) ^ 2)
        * sg_grpSum (fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) f g) ^ 2)
        ≤ 2 * (q : ℝ) ^ 2 * (K * D / 2) := by
      have h5 : 2 * (q : ℝ) ^ 2 * (K * D / 2) = K * (q : ℝ) ^ 2 * D := by ring
      rw [h5, ← h1]
      exact hcol
    exact (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * (q : ℝ) ^ 2)).mp h4
  calc (∑ g, (f (sg_colU (q := q) (a := a) (b := b) (c := c) s t * g) - f g) ^ 2)
      ≤ 4 * ∑ g, (f g - (1 / (q : ℝ) ^ 2)
          * sg_grpSum (fun s t => sg_colU (q := q) (a := a) (b := b) (c := c) s t) f g) ^ 2 := h2
    _ ≤ 4 * (K * D / 2) := by linarith
    _ = 2 * K * D := by ring

end Column


/-! ## 4. Telescoping along a word -/

/-- `(a+b)^2 ≤ 2(a²+b²)`. -/
private lemma sg_sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- The weighted Cauchy–Schwarz pointwise inequality: `(a+b)² ≤ (1+t)a² + (1+1/t)b²`. -/
private lemma sg_sq_add_le_weighted (a b t : ℝ) (ht : 0 < t) :
    (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 := by
  have h := sq_nonneg (a * t - b)
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp
  nlinarith [h]

section Telescope

variable {G : Type*} [Group G] [Fintype G]

/-- Telescoping bound along a word: if each letter moves `F` by at most `B` in `ℓ²`, then the
product moves `F` by at most `(length)² B`. -/
private lemma sg_list_telescope_bound (F : G → ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∀ (l : List G), (∀ x ∈ l, ∑ g, (F (x * g) - F g) ^ 2 ≤ B) →
      ∑ g, (F (l.prod * g) - F g) ^ 2 ≤ ((l.length : ℝ)) ^ 2 * B := by
  intro l
  induction l with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hl
      have hx : ∑ g, (F (x * g) - F g) ^ 2 ≤ B := hl x (by simp)
      have hxs : ∀ y ∈ xs, ∑ g, (F (y * g) - F g) ^ 2 ≤ B := fun y hy => hl y (by simp [hy])
      have hih := ih hxs
      by_cases hlen : xs.length = 0
      · obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
        simpa using hx
      · have hlt : (0 : ℝ) < (xs.length : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hlen
        have hpt : ∀ g : G, (F ((x * xs.prod) * g) - F g) ^ 2
            ≤ (1 + (xs.length : ℝ)) * (F (x * (xs.prod * g)) - F (xs.prod * g)) ^ 2
              + (1 + 1 / (xs.length : ℝ)) * (F (xs.prod * g) - F g) ^ 2 := by
          intro g
          rw [mul_assoc]
          have hid : F (x * (xs.prod * g)) - F g
              = (F (x * (xs.prod * g)) - F (xs.prod * g)) + (F (xs.prod * g) - F g) := by
            ring
          rw [hid]
          exact sg_sq_add_le_weighted _ _ _ hlt
        have hre : (∑ g, (F (x * (xs.prod * g)) - F (xs.prod * g)) ^ 2)
            = ∑ g, (F (x * g) - F g) ^ 2 := by
          refine Fintype.sum_equiv (Equiv.mulLeft xs.prod)
            (fun g => (F (x * (xs.prod * g)) - F (xs.prod * g)) ^ 2)
            (fun g => (F (x * g) - F g) ^ 2) ?_
          intro g
          simp only [Equiv.coe_mulLeft]
        calc ∑ g, (F ((x * xs.prod) * g) - F g) ^ 2
            ≤ ∑ g, ((1 + (xs.length : ℝ)) * (F (x * (xs.prod * g)) - F (xs.prod * g)) ^ 2
                + (1 + 1 / (xs.length : ℝ)) * (F (xs.prod * g) - F g) ^ 2) :=
              Finset.sum_le_sum fun g _ => hpt g
          _ = (1 + (xs.length : ℝ)) * (∑ g, (F (x * (xs.prod * g)) - F (xs.prod * g)) ^ 2)
                + (1 + 1 / (xs.length : ℝ)) * (∑ g, (F (xs.prod * g) - F g) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = (1 + (xs.length : ℝ)) * (∑ g, (F (x * g) - F g) ^ 2)
                + (1 + 1 / (xs.length : ℝ)) * (∑ g, (F (xs.prod * g) - F g) ^ 2) := by
              rw [hre]
          _ ≤ (1 + (xs.length : ℝ)) * B
                + (1 + 1 / (xs.length : ℝ)) * ((xs.length : ℝ) ^ 2 * B) := by
              have h1 : (0 : ℝ) ≤ 1 + (xs.length : ℝ) := by positivity
              have h2 : (0 : ℝ) ≤ 1 + 1 / (xs.length : ℝ) := by positivity
              nlinarith [h1, h2, hx, hih]
          _ = (((xs.length : ℝ) + 1)) ^ 2 * B := by
              have hℓ : (xs.length : ℝ) ≠ 0 := ne_of_gt hlt
              field_simp
              ring
          _ = ((↑(x :: xs).length : ℝ)) ^ 2 * B := by
              rw [List.length_cons, Nat.cast_add, Nat.cast_one]

end Telescope

/-! ## 5. Averaging over the whole group -/

section WholeGroup

variable {G : Type*} [Group G] [Fintype G]

/-- `∑_h ∑_g (F (h*g) - F g)² = 2|G| ∑ F² - 2 (∑ F)²`. -/
private lemma sg_sum_L2_id (F : G → ℝ) :
    (∑ h : G, ∑ g, (F (h * g) - F g) ^ 2)
      = 2 * (Fintype.card G : ℝ) * (∑ g, F g ^ 2) - 2 * (∑ g, F g) ^ 2 := by
  have hterm : ∀ h g : G, (F (h * g) - F g) ^ 2
      = F (h * g) ^ 2 - 2 * (F (h * g) * F g) + F g ^ 2 := fun h g => by ring
  have hA : (∑ h : G, ∑ g, F (h * g) ^ 2) = (Fintype.card G : ℝ) * ∑ g, F g ^ 2 := by
    have h : ∀ h : G, (∑ g, F (h * g) ^ 2) = ∑ g, F g ^ 2 :=
      fun h => sg_sum_mulLeft h (fun g => F g ^ 2)
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hC : (∑ _h : G, ∑ g, F g ^ 2) = (Fintype.card G : ℝ) * ∑ g, F g ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hB : (∑ h : G, ∑ g, 2 * (F (h * g) * F g)) = 2 * (∑ g, F g) ^ 2 := by
    have e1 : (∑ h : G, ∑ g, 2 * (F (h * g) * F g)) = 2 * ∑ h : G, ∑ g, F (h * g) * F g := by
      simp only [Finset.mul_sum]
    rw [e1, Finset.sum_comm]
    congr 1
    have hre : ∀ g : G, (∑ h : G, F (h * g)) = ∑ h, F h := fun g => sg_sum_mulRight g F
    calc ∑ g, ∑ h, F (h * g) * F g
        = ∑ g, F g * ∑ h, F (h * g) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [← Finset.sum_mul, mul_comm]
      _ = ∑ g, F g * ∑ h, F h := by simp only [hre]
      _ = (∑ g, F g) ^ 2 := by rw [sq, ← Finset.sum_mul]
  rw [show (∑ h : G, ∑ g, (F (h * g) - F g) ^ 2)
      = ∑ h : G, ∑ g, (F (h * g) ^ 2 - 2 * (F (h * g) * F g) + F g ^ 2) by
    simp only [hterm]]
  simp only [sg_sum_split3]
  rw [hA, hB, hC]
  ring

end WholeGroup


/-! ## 6. From a single transvection to all of `G` -/

section Final

/-- The column bound propagates to an arbitrary elementary transvection. -/
private lemma sg_transvection_bound {q : ℕ} [Fact q.Prime] {K D : ℝ}
    {f : Matrix.SpecialLinearGroup (Fin 3) (ZMod q) → ℝ}
    (hcol : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      (∑ s : ZMod q, ∑ t : ZMod q, ∑ g, (f (sl3E q a c s * sl3E q b c t * g) - f g) ^ 2)
        ≤ K * (q : ℝ) ^ 2 * D)
    (i j : Fin 3) (hij : i ≠ j) (t : ZMod q) :
    (∑ g, (f (sl3E q i j t * g) - f g) ^ 2) ≤ 2 * K * D := by
  obtain ⟨c, hic, hjc⟩ : ∃ c : Fin 3, c ≠ i ∧ c ≠ j := by
    revert i j
    decide
  have h := sg_col_bound_single (q := q) (a := i) (b := c) (c := j) hij hjc
    (hcol i c j hic.symm hij hjc) t 0
  have hcolU : sg_colU (q := q) (a := i) (b := c) (c := j) t 0 = sl3E q i j t := by
    rw [sg_colU, sg_sl3E_zero c j hjc, mul_one]
  rwa [hcolU] at h

/-- **Assembly**: relative property (T) for the column subgroup together with bounded
elementary generation gives the uniform spectral gap. -/
theorem sl3_gap_of {K : ℝ} (hK : 0 < K) (hcol : sl3RelT K) (L : ℕ) (hL : sl3BoundedGen L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ, ∑ g, f g = 0 →
        c * ∑ g, f g ^ 2 ≤ sl3DF p f := by
  have hCpos : (0 : ℝ) < (((max L 1 : ℕ)) : ℝ) := by
    have : 0 < max L 1 := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
    exact_mod_cast this
  refine ⟨1 / (K * (((max L 1 : ℕ)) : ℝ) ^ 2), by positivity, ?_⟩
  intro p hpprime hne f hf
  haveI := hpprime
  have hL' : sl3BoundedGen (max L 1) := by
    intro q hq g
    obtain ⟨l, hlen, hne, hg⟩ := hL q g
    exact ⟨l, le_trans hlen (le_max_left _ _), hne, hg⟩
  have hDnn : (0 : ℝ) ≤ sl3DF p f := by
    rw [sl3DF]; positivity
  have hcol' : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      (∑ s : ZMod p, ∑ t : ZMod p, ∑ g, (f (sl3E p a c s * sl3E p b c t * g) - f g) ^ 2)
        ≤ K * (p : ℝ) ^ 2 * sl3DF p f := fun a b c hab hac hbc => hcol p hne a b c hab hac hbc f
  have htb := sg_transvection_bound (q := p) hcol'
  have hB : (0 : ℝ) ≤ 2 * K * sl3DF p f := by positivity
  have hall : ∀ h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
      (∑ g, (f (h * g) - f g) ^ 2)
        ≤ (((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f) := by
    intro h
    obtain ⟨l, hlen, hne, hg⟩ := hL' p h
    let l' : List (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :=
      l.map (fun x => sl3E p x.1 x.2.1 x.2.2)
    have hprod : l'.prod = h := by
      rw [← hg]
    have hlen' : l'.length ≤ max L 1 := by simpa [l'] using hlen
    have hEl : ∀ x ∈ l', (∑ g, (f (x * g) - f g) ^ 2) ≤ 2 * K * sl3DF p f := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact htb y.1 y.2.1 (hne y hy) y.2.2
    have htelescope := sg_list_telescope_bound f hB l' hEl
    rw [hprod] at htelescope
    refine htelescope.trans ?_
    have h1 : (l'.length : ℝ) ≤ (((max L 1 : ℕ)) : ℝ) := by exact_mod_cast hlen'
    have h2 : (0 : ℝ) ≤ (l'.length : ℝ) := by positivity
    have hsq : (l'.length : ℝ) ^ 2 ≤ ((((max L 1 : ℕ)) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    exact mul_le_mul_of_nonneg_right hsq hB
  have hgs : (∑ h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p), ∑ g, (f (h * g) - f g) ^ 2)
      = 2 * (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ) * (∑ g, f g ^ 2) := by
    rw [sg_sum_L2_id f, hf]; ring
  have hcardpos : (0 : ℝ) < (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hupper : (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
        * (2 * (∑ g, f g ^ 2))
      ≤ (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
        * ((((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f)) := by
    have hsum : (∑ h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
          ∑ g, (f (h * g) - f g) ^ 2)
        ≤ (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
          * ((((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f)) := by
      calc (∑ h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p), ∑ g, (f (h * g) - f g) ^ 2)
          ≤ ∑ _h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p),
              ((((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f)) :=
            Finset.sum_le_sum fun h _ => hall h
        _ = (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
              * ((((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hgs] at hsum
    calc (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
          * (2 * (∑ g, f g ^ 2))
        = 2 * (Fintype.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℝ)
            * (∑ g, f g ^ 2) := by ring
      _ ≤ _ := hsum
  have hkey : 2 * (∑ g, f g ^ 2) ≤ (((max L 1 : ℕ)) : ℝ) ^ 2 * (2 * K * sl3DF p f) :=
    (mul_le_mul_iff_of_pos_left hcardpos).mp hupper
  have h2 : (∑ g, f g ^ 2) ≤ K * (((max L 1 : ℕ)) : ℝ) ^ 2 * sl3DF p f := by
    have h3 : 2 * (∑ g, f g ^ 2) ≤ 2 * (K * (((max L 1 : ℕ)) : ℝ) ^ 2 * sl3DF p f) := by
      nlinarith [hkey]
    exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp h3
  have hC2 : (0 : ℝ) < K * (((max L 1 : ℕ)) : ℝ) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hC2]
  nlinarith [h2]

end Final


/-! ## 7. The spectral gap -/

/-- **Uniform spectral gap of `Cay(SL₃(ℤ/p), {E_ij(±1)})`.** For mean-zero `f`, the Dirichlet
form over the 12 generators is at least `c ∑ f²`, with `c > 0` independent of the odd prime
`p`. -/
theorem sl3_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ, ∑ g, f g = 0 →
        c * ∑ g, f g ^ 2 ≤ ∑ k, ∑ g, (f (sl3Gen p k * g) - f g) ^ 2 := by
  obtain ⟨K, hK, hcol⟩ := sl3_gap_relT
  obtain ⟨L, hL⟩ := sl3_bounded_generation
  have hrelT : sl3RelT K := by
    intro p hp hp2 a b c hab hac hbc f
    haveI := hp
    exact hcol p hp2 a b c hab hac hbc f
  obtain ⟨c, hc, hmain⟩ := sl3_gap_of (K := K) hK hrelT L hL
  refine ⟨c, hc, ?_⟩
  intro p hp hp2 f hf
  haveI := hp
  exact hmain p hp2 f hf

end Work.LT
