/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The radial (one-sided) Seeley construction for the disc: definitions

This file contains the definitions used by `Work.NN.Final.one_sided_disc_extension`: the
finite radial Seeley construction extending a function from the unit disc `ball(0,1) ⊂ ℂ` to a
larger disc `ball(0,c)`, in a `U`-parametrised setting `U × ℂ` (with `U ⊆ X` open).

The construction is: for `‖z‖ > 1`,

`G(x,z) = ∑_{m ∉ S} a m * χ (b m * (‖z‖ - 1)) * g (x, ρ_m z)`,

where `ρ_m z` is the point of the ray through `z` whose radius is `1 - b m * (‖z‖ - 1)` (the
*affine* radial reflection), `χ` is a smooth cutoff which is `1` near `0` and vanishes outside
`[-2,2]`, and the weights `a m` are the Lagrange weights at the nodes `-(b m)` (`m ≤ k`), so that
the moment identities `∑_{m ≤ k} a m * (-(b m))^j = 1` (`j ≤ k`) hold.  By the moment identities
the jets of the extension match those of `g` to order `k` across the sphere, which is what makes
the extension `C^k`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Seeley.Setup

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter
open Polynomial

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Scales, reflection, terms -/

/-- The scales of the finite radial Seeley construction at order `k`: `b m = m + 2`. -/
def discScale (m : ℕ) : ℝ := (m : ℝ) + 2

lemma discScale_pos (m : ℕ) : 0 < discScale m := by
  rw [discScale]; positivity

/-- The affine radial reflection: the point of the ray through `z` whose radius is
`1 - b * (‖z‖ - 1)`. -/
def discRefl (b : ℝ) (z : ℂ) : ℂ := ((1 - b * (‖z‖ - 1)) / ‖z‖ : ℝ) • z

/-- The `m`-th term of the finite radial Seeley sum. -/
def discTerm (a b : ℕ → ℝ) (g : X × ℂ → ℂ) (m : ℕ) (p : X × ℂ) : ℂ :=
  (a m) • ((seeleyCut (b m * (‖p.2‖ - 1))) • g (p.1, discRefl (b m) p.2))

/-- The finite radial Seeley sum. -/
def discSum (k : ℕ) (a b : ℕ → ℝ) (g : X × ℂ → ℂ) (p : X × ℂ) : ℂ :=
  ∑ m ∈ Finset.range (k + 1), discTerm a b g m p

/-- The boundary value of the extension on the sphere: the limit of `g` along the radial
approach.  (Any `C^k` extension agreeing with `g` on the open unit ball must take this value on
the sphere.) -/
def discBdry (g : X × ℂ → ℂ) (p : X × ℂ) : ℂ :=
  Filter.limUnder (𝓝[<] (1 : ℝ)) (fun s : ℝ => g (p.1, s • p.2))

/-- The one-sided radial Seeley extension of `g` from the unit disc. -/
def discExt (k : ℕ) (a b : ℕ → ℝ) (g : X × ℂ → ℂ) (p : X × ℂ) : ℂ :=
  if ‖p.2‖ < 1 then g p else if ‖p.2‖ = 1 then discBdry g p else discSum k a b g p

/-! ## The Lagrange moment weights -/

/-- The Lagrange weights at the nodes `-(discScale m)`: the coefficients of the (finite)
Lagrange interpolation functional at the point `1`.  They satisfy the moment identities
`∑_{m ≤ k} discWt k m * (-(discScale m))^j = 1` for `j ≤ k`. -/
noncomputable def discWt (k : ℕ) (m : ℕ) : ℝ :=
  if h : m < k + 1 then
    (Lagrange.basis Finset.univ (fun i : Fin (k + 1) => -(discScale i)) ⟨m, h⟩).eval 1
  else 0

lemma discWt_of_lt (k m : ℕ) (h : m < k + 1) :
    discWt k m =
      (Lagrange.basis Finset.univ (fun i : Fin (k + 1) => -(discScale i)) ⟨m, h⟩).eval 1 :=
  dif_pos h

/-- The Lagrange moment identity: for distinct nodes `c`, the interpolation functional at
the point `1` reproduces `p ↦ p 1` on polynomials of degree `≤ k`. -/
theorem lagrange_moment (k : ℕ) (c : Fin (k+1) → ℝ) (hc : Function.Injective c) :
    ∀ j ≤ k, (∑ m, (Lagrange.basis Finset.univ c m).eval 1 * (c m)^j) = 1 := by
  classical
  intro j hj
  have hcard : (Finset.univ : Finset (Fin (k+1))).card = k+1 :=
    Finset.card_univ.trans (Fintype.card_fin _)
  set R : ℝ[X] := ∑ m : Fin (k+1), Polynomial.C ((Polynomial.X ^ j).eval (c m)) *
      Lagrange.basis Finset.univ c m with hR
  have hRdeg : R.degree < ((Finset.univ : Finset (Fin (k+1))).card : WithBot ℕ) := by
    rw [hcard, hR]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro i _
    have h2 : (Lagrange.basis Finset.univ c i).degree = ((k+1) - 1 : ℕ) := by
      rw [Lagrange.degree_basis (s := Finset.univ) (v := c) hc.injOn (Finset.mem_univ i), hcard]
    calc (Polynomial.C ((Polynomial.X ^ j).eval (c i)) * Lagrange.basis Finset.univ c i).degree
        ≤ (Polynomial.C ((Polynomial.X ^ j).eval (c i))).degree
            + (Lagrange.basis Finset.univ c i).degree := Polynomial.degree_mul_le _ _
      _ ≤ (0 : WithBot ℕ) + (((k+1) - 1 : ℕ) : WithBot ℕ) := by
          rw [h2]; exact add_le_add Polynomial.degree_C_le le_rfl
      _ < ((k+1 : ℕ) : WithBot ℕ) := by
          rw [zero_add]
          exact_mod_cast (Nat.pred_lt (Nat.succ_ne_zero k))
  have hReq : ∀ i, R.eval (c i) = (Polynomial.X ^ j).eval (c i) := by
    intro i
    rw [hR, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single i]
    · rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_basis_self (s := Finset.univ)
        (v := c) hc.injOn (Finset.mem_univ i), mul_one]
    · intro b _ hb
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        Lagrange.eval_basis_of_ne (s := Finset.univ) hb (Finset.mem_univ i), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hqdeg : (Polynomial.X ^ j : ℝ[X]).degree <
      ((Finset.univ : Finset (Fin (k+1))).card : WithBot ℕ) := by
    rw [hcard, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hj
  have hRq : R = Polynomial.X ^ j := Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    hc.injOn hRdeg hqdeg (fun i _ => hReq i)
  calc ∑ m, (Lagrange.basis Finset.univ c m).eval 1 * (c m)^j
      = R.eval 1 := by
        rw [hR, Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        ring
    _ = (Polynomial.X ^ j : ℝ[X]).eval 1 := by rw [hRq]
    _ = 1 := by rw [Polynomial.eval_pow, Polynomial.eval_X, one_pow]

/-- Any finite system of distinct nodes admits weights reproducing the functional `p ↦ p 1` on
polynomials of degree `≤ k`. -/
theorem exists_moment_weights (k : ℕ) (c : Fin (k+1) → ℝ) (hc : Function.Injective c) :
    ∃ a : Fin (k+1) → ℝ, ∀ j ≤ k, ∑ m, a m * (c m)^j = 1 :=
  ⟨_, lagrange_moment k c hc⟩

/-- The moment identities for the Lagrange weights. -/
theorem discWt_moment (k : ℕ) {j : ℕ} (hj : j ≤ k) :
    ∑ m ∈ Finset.range (k + 1), discWt k m * (-(discScale m)) ^ j = 1 := by
  classical
  have hinj : Function.Injective (fun i : Fin (k+1) => -(discScale i)) := by
    intro i i' h
    have h' : discScale i = discScale i' := neg_injective h
    rw [discScale, discScale] at h'
    have : (i : ℝ) = (i' : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast this)
  have hfw : ∀ i : Fin (k+1), discWt k i =
      (Lagrange.basis Finset.univ (fun i : Fin (k+1) => -(discScale i)) i).eval 1 := by
    intro i
    simp only [discWt, dif_pos i.isLt]
  have hfin : (∑ i : Fin (k+1), discWt k i * (-(discScale i))^j) = 1 := by
    rw [← lagrange_moment k (fun i : Fin (k+1) => -(discScale i)) hinj j hj]
    exact Finset.sum_congr rfl fun i _ => by rw [hfw i]
  rwa [Fin.sum_univ_eq_sum_range (fun m => discWt k m * (-(discScale m))^j) (k+1)] at hfin


/-- Consequence of the moment identities: `∑_m discWt k m * (discScale m)^j = (-1)^j`. -/
lemma discWt_moment' (k : ℕ) {j : ℕ} (hj : j ≤ k) :
    ∑ m ∈ Finset.range (k+1), discWt k m * (discScale m)^j = (-1)^j := by
  have h := discWt_moment k hj
  have h2 : ∀ m ∈ Finset.range (k+1), discWt k m * (discScale m)^j
      = (-1)^j * (discWt k m * (-(discScale m))^j) := by
    intro m _
    have h1 : (-(discScale m))^j = (-1:ℝ)^j * (discScale m)^j := by rw [neg_pow]
    rw [h1]
    rw [show (-1:ℝ)^j * (discWt k m * ((-1:ℝ)^j * (discScale m)^j))
        = ((-1:ℝ)^j * (-1:ℝ)^j) * (discWt k m * (discScale m)^j) by ring]
    rw [← pow_add, Even.neg_one_pow (⟨j, by ring⟩ : Even (j+j)), one_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, h, mul_one]

/-- The "shifted" moment identities: `∑_m discWt k m * (discScale m + 1)^p = δ_{p0}` for
`p ≤ k`.  This is the algebraic core of the jet matching at the sphere: the displacement of the
reflected point is `- (discScale m + 1) * (‖z‖ - 1) * u`. -/
lemma discWt_moment_shift (k : ℕ) {p : ℕ} (hp : p ≤ k) :
    ∑ m ∈ Finset.range (k+1), discWt k m * (discScale m + 1)^p
      = if p = 0 then 1 else 0 := by
  have hbin : ∀ m : ℕ, (discScale m + 1)^p
      = ∑ j ∈ Finset.range (p+1), (p.choose j : ℝ) * (discScale m)^j := by
    intro m
    rw [add_pow]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [one_pow, mul_one]
    ring
  calc ∑ m ∈ Finset.range (k+1), discWt k m * (discScale m + 1)^p
      = ∑ m ∈ Finset.range (k+1), ∑ j ∈ Finset.range (p+1),
          (p.choose j : ℝ) * (discWt k m * (discScale m)^j) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hbin m, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j ∈ Finset.range (p+1), (p.choose j : ℝ) *
          (∑ m ∈ Finset.range (k+1), discWt k m * (discScale m)^j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range (p+1), (p.choose j : ℝ) * (-1)^j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [discWt_moment' k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp)]
    _ = if p = 0 then 1 else 0 := by
        rcases Nat.eq_zero_or_pos p with hp0 | hppos
        · subst hp0; simp
        · rw [if_neg (Nat.pos_iff_ne_zero.mp hppos)]
          have h1 : (∑ j ∈ Finset.range (p+1), (p.choose j : ℝ) * (-1)^j) = (-1 + 1)^p := by
            rw [add_pow (-1:ℝ) 1 p]
            refine Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one]; ring
          rw [h1, show (-1:ℝ) + 1 = 0 by norm_num,
            zero_pow (Nat.pos_iff_ne_zero.mp hppos)]

/-- The displacement of the reflected point, written as a multiple of the radial unit vector. -/
lemma discRefl_sub_self {b : ℝ} {z : ℂ} (hz : z ≠ 0) :
    discRefl b z - z = (-((b + 1) * (‖z‖ - 1)) / ‖z‖ : ℝ) • z := by
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h : (1 - b * (‖z‖ - 1)) / ‖z‖ - 1 = (-((b + 1) * (‖z‖ - 1))) / ‖z‖ := by
    field_simp; ring
  rw [discRefl, ← h, sub_smul, one_smul]

/-- On the sphere the reflection is the identity. -/
lemma discRefl_eq_self {b : ℝ} {z : ℂ} (hz : ‖z‖ = 1) : discRefl b z = z := by
  rw [discRefl, hz]
  norm_num

/-! ## Elementary properties -/

/-- The extension agrees with `g` on the open unit disc. -/
lemma discExt_of_norm_lt_one {k : ℕ} {a b : ℕ → ℝ} {g : X × ℂ → ℂ} {p : X × ℂ}
    (hp : ‖p.2‖ < 1) : discExt k a b g p = g p := ite_eq_left hp

/-- The reflection is smooth away from the origin. -/
lemma contDiffOn_discRefl (b : ℝ) : ContDiffOn ℝ ⊤ (discRefl b) {z : ℂ | z ≠ 0} := by
  intro z hz
  have hz' : z ≠ 0 := hz
  have hnorm : ContDiffWithinAt ℝ ⊤ (fun w : ℂ => ‖w‖) {z : ℂ | z ≠ 0} z :=
    ContDiffWithinAt.norm ℝ contDiffWithinAt_id (by simpa using hz')
  unfold discRefl
  have h1 : ContDiffWithinAt ℝ ⊤ (fun w : ℂ => (1 - b * (‖w‖ - 1)) / ‖w‖) {z : ℂ | z ≠ 0} z := by
    apply ContDiffWithinAt.div
    · exact contDiffWithinAt_const.sub
        (contDiffWithinAt_const.mul (hnorm.sub contDiffWithinAt_const))
    · exact hnorm
    · simpa using hz'
  exact h1.smul contDiffWithinAt_id

/-- The modulus of the reflected point. -/
lemma norm_discRefl (b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖discRefl b z‖ = |1 - b * (‖z‖ - 1)| := by
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [discRefl, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (le_of_lt hn),
    div_mul_cancel₀ _ (ne_of_gt hn)]

/-- If `1 < ‖z‖` and `b * (‖z‖ - 1) < 2` then the reflected point lies strictly inside the unit
disc. -/
lemma norm_discRefl_lt_one {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 1 < ‖z‖)
    (h2 : b * (‖z‖ - 1) < 2) : ‖discRefl b z‖ < 1 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp only [norm_zero] at hz; linarith
  rw [norm_discRefl b hz0]
  have hδ : 0 < ‖z‖ - 1 := by linarith
  have hbδ : 0 < b * (‖z‖ - 1) := mul_pos hb hδ
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

end Work.NN.Final
