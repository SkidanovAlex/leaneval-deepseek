import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLComp.exists_isCompact_image

/-!
# Uniform injectivity of the orbit map on compacta (clause 4 of `P_X3`)

For a compact subset `K` of `X₃ = SL₃(ℝ)/SL₃(ℤ)` there is `η > 0` such that `g • x = h • x`
with `g, h ∈ V η` and `x ∈ K` forces `g = h`.

The mathematical content is the *local freeness* of the action of the discrete group `Γ₃`,
uniformly on compacta.  The proof is the standard one:

* a compact `K` is covered by the image of a compact `C ⊆ SL₃(ℝ)` (`exists_isCompact_image`);
* the stabiliser of `x = mkX s` is `s Γ₃ s⁻¹`, so `g • x = h • x` means
  `(h s)⁻¹ (g s) ∈ Γ₃`; if `g, h` are close to `1` and `s ∈ C` then this element of `Γ₃` is
  close to `1`, and since the entries of an element of `Γ₃` are integers, the only element of
  `Γ₃` whose entries are all within `1/2` of the identity is `1` (`Γ₃` is discrete).

The only quantitative estimate needed is that entries of products of `3 × 3` matrices are
controlled by the entries of the factors (`mat3_mul_entry_bound`); the entries of the relevant
matrices are bounded on a compact set (`entry_bound_compact`).
-/

namespace Work.EKLComp

open Work.EKLContract

/-- `V δ` is monotone in `δ`. -/
lemma V_mono' {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' := fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- Entrywise bound for the product of two `3 × 3` matrices. -/
lemma mat3_mul_entry_bound (M N : Matrix (Fin 3) (Fin 3) ℝ) {C D : ℝ}
    (hM : ∀ i j, |M i j| ≤ C) (hN : ∀ i j, |N i j| ≤ D) (i j : Fin 3) :
    |(M * N) i j| ≤ 3 * C * D := by
  rw [Matrix.mul_apply]
  calc |∑ k, M i k * N k j| ≤ ∑ k, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |M i k| * |N k j| := by simp [abs_mul]
    _ ≤ ∑ k, C * D := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) (le_trans (abs_nonneg _) (hM i k))
    _ = 3 * C * D := by rw [Fin.sum_univ_three]; ring

/-- On a compact set of `SL₃(ℝ)` the entries of `u` and of `u⁻¹` are bounded by a single
constant `A ≥ 1`. -/
lemma entry_bound_compact {D : Set SL3} (hD : IsCompact D) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ u ∈ D, ∀ i j, |toMat u i j| ≤ A ∧ |toMat u⁻¹ i j| ≤ A := by
  have hcont : ContinuousOn (fun u : SL3 => ∑ i, ∑ j, (|toMat u i j| + |toMat u⁻¹ i j|)) D := by
    refine Continuous.continuousOn ?_
    fun_prop
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, le_max_right _ _, fun u hu i j => ?_⟩
  have hnonneg : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hFC : (∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|)) ≤ C := by
    have h' : ‖∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|)‖ ≤ C := hC u hu
    rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg] at h'
  have hstep1 : |toMat u i j| + |toMat u⁻¹ i j| ≤
      ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|) :=
    Finset.single_le_sum (fun j' _ => show (0:ℝ) ≤ |toMat u i j'| + |toMat u⁻¹ i j'| by positivity)
      (Finset.mem_univ j)
  have hstep2 : (∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|)) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|) :=
    Finset.single_le_sum
      (fun i' _ => Finset.sum_nonneg fun j' _ =>
        show (0:ℝ) ≤ |toMat u i' j'| + |toMat u⁻¹ i' j'| by positivity)
      (Finset.mem_univ i)
  have hinner := le_trans hstep1 hstep2
  have h1 : |toMat u i j| ≤ ∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|) :=
    le_trans (le_add_of_nonneg_right (abs_nonneg _)) hinner
  have h2 : |toMat u⁻¹ i j| ≤ ∑ i : Fin 3, ∑ j : Fin 3, (|toMat u i j| + |toMat u⁻¹ i j|) :=
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) hinner
  exact ⟨le_trans h1 (le_trans hFC (le_max_left _ _)),
    le_trans h2 (le_trans hFC (le_max_left _ _))⟩

/-- **Discreteness of `Γ₃`, quantitatively.**  The entries of an element of `Γ₃` are integers;
hence an element of `Γ₃` all of whose entries are within `1/2` of the identity is the
identity. -/
lemma gamma3_half (γ : SL3) (hγ : γ ∈ Γ3) (hV : γ ∈ V (1/2)) : γ = 1 := by
  have hV' : ∀ i j, |(γ : Matrix (Fin 3) (Fin 3) ℝ) i j -
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 1/2 := hV
  apply ext_toMat
  rw [toMat_one]
  ext i j
  rw [toMat_apply]
  obtain ⟨k, hk⟩ := Work.EKLContract.Lemmas.Γ3_integral_entries γ hγ i j
  rw [hk]
  have h := hV' i j
  rw [hk] at h
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h
    have hk1 : k = 1 := by
      have h2 : |((k - 1 : ℤ) : ℝ)| < 1 := by
        rw [show ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 by push_cast; ring]
        rw [abs_lt] at h ⊢
        constructor <;> linarith [h.1, h.2]
      have h3 : |(k - 1 : ℤ)| < 1 := by exact_mod_cast h2
      have h4 : k - 1 = 0 := Int.abs_lt_one_iff.mp h3
      omega
    rw [hk1, Matrix.one_apply_eq]
    norm_num
  · rw [Matrix.one_apply_ne hij] at h
    have hk0 : k = 0 := by
      have h2 : |(k : ℝ)| < 1 := by
        rw [abs_lt] at h ⊢
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      have h3 : |(k : ℤ)| < 1 := by exact_mod_cast h2
      exact Int.abs_lt_one_iff.mp h3
    rw [hk0, Matrix.one_apply_ne hij]
    norm_num

theorem uniform_inj_of_isCompact (K : Set Work.EKLContract.X3) (hK : IsCompact K) : ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ g h : Work.EKLContract.SL3, g ∈ Work.EKLContract.V η → h ∈ Work.EKLContract.V η → g • x = h • x → g = h := by
  obtain ⟨Ccpt, hCcpt, hKC⟩ := exists_isCompact_image K hK
  -- an entrywise compact box containing `V 1`
  set B : Set SL3 := {g | ∀ i j, ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 1) ≤ g i j ∧
    g i j ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)} with hBdef
  have hBcpt : IsCompact B := Work.EKLProd.sl3EntryBox_compact _ _
  have hVB : V 1 ⊆ B := by
    intro g hg i j
    have h := hg i j
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have honeB : (1 : SL3) ∈ B := by
    intro i j
    constructor <;> simp
  -- the compact set of all matrices whose entries and inverse-entries we bound
  set D : Set SL3 := (fun p : SL3 × SL3 => p.1 * p.2) '' (B ×ˢ Ccpt) with hDdef
  have hDcpt : IsCompact D := (hBcpt.prod hCcpt).image (by fun_prop)
  obtain ⟨A, hA1, hAb⟩ := entry_bound_compact hDcpt
  by_contra hcon
  push_neg at hcon
  -- a sequence of counterexamples
  have key : ∀ n : ℕ, ∃ x : X3, ∃ g : SL3, ∃ h : SL3,
      x ∈ K ∧ g ∈ V (1 / ((n : ℝ) + 1)) ∧ h ∈ V (1 / ((n : ℝ) + 1)) ∧
        g • x = h • x ∧ g ≠ h := by
    intro n
    obtain ⟨xx, hx, gg, hh, hgv, hhv, hgh, hne⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨xx, gg, hh, hx, hgv, hhv, hgh, hne⟩
  choose x g h hxK hg hh hgh hne using key
  -- representatives of the `x n` in the compact set `C`
  have hrep : ∀ n : ℕ, ∃ s : SL3, s ∈ Ccpt ∧ mkX s = x n := fun n => hKC (hxK n)
  choose s hsC hsx using hrep
  -- the index at which the estimates become strong enough
  obtain ⟨N, hNgt⟩ := exists_nat_gt (36 * A ^ 2)
  have hNlt : 36 * A ^ 2 < (N : ℝ) + 1 := by linarith
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hle1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  -- membership of the relevant products in `D`
  have hhN1 : h N ∈ V 1 := V_mono' hle1 (hh N)
  have hgN1 : g N ∈ V 1 := V_mono' hle1 (hg N)
  have huD : h N * s N ∈ D := ⟨(h N, s N), ⟨hVB hhN1, hsC N⟩, rfl⟩
  have hsD : s N ∈ D := ⟨(1, s N), ⟨honeB, hsC N⟩, by simp⟩
  -- the matrix identity behind the estimate
  have hkey1 : toMat ((h N * s N)⁻¹ * (g N * s N)) - (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = toMat ((h N * s N)⁻¹) * (toMat (g N * s N) - toMat (h N * s N)) := by
    have h1 : toMat ((h N * s N)⁻¹) * toMat (h N * s N) = 1 := by
      rw [← toMat_mul, inv_mul_cancel, toMat_one]
    have h2 : toMat ((h N * s N)⁻¹) * (toMat (g N * s N) - toMat (h N * s N))
        = toMat ((h N * s N)⁻¹) * toMat (g N * s N) - 1 := by
      rw [Matrix.mul_sub, h1]
    rw [toMat_mul, h2]
  have hkey2 : toMat (g N * s N) - toMat (h N * s N)
      = (toMat (g N) - toMat (h N)) * toMat (s N) := by
    simp only [toMat_mul, Matrix.sub_mul]
  -- the estimate
  have hMb : ∀ k l, |(toMat (g N) - toMat (h N)) k l| ≤ 2 * (1 / ((N : ℝ) + 1)) := by
    intro k l
    have h1 := hg N k l
    have h2 := hh N k l
    rw [abs_lt] at h1 h2
    rw [Matrix.sub_apply]
    exact le_of_lt (by rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
  have hWb : ∀ k l, |((toMat (g N) - toMat (h N)) * toMat (s N)) k l|
      ≤ 3 * (2 * (1 / ((N : ℝ) + 1))) * A :=
    fun k l => mat3_mul_entry_bound _ _ (fun k l => hMb k l)
      (fun l j => (hAb (s N) hsD l j).1) k l
  have hfinal : ∀ i j, |(toMat ((h N * s N)⁻¹) *
      ((toMat (g N) - toMat (h N)) * toMat (s N))) i j|
      ≤ 3 * A * (3 * (2 * (1 / ((N : ℝ) + 1))) * A) :=
    fun i j => mat3_mul_entry_bound _ _ (fun i k => (hAb (h N * s N) huD i k).2)
      (fun k l => hWb k l) i j
  have harch : 18 * A ^ 2 * (1 / ((N : ℝ) + 1)) < 1 / 2 := by
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith [hNlt]
  have hbound : (h N * s N)⁻¹ * (g N * s N) ∈ V (1 / 2) := by
    intro i j
    show |(toMat ((h N * s N)⁻¹ * (g N * s N)) -
      (1 : Matrix (Fin 3) (Fin 3) ℝ)) i j| < 1 / 2
    rw [hkey1, hkey2]
    exact lt_of_le_of_lt (hfinal i j) (by nlinarith [harch])
  -- the element of `Γ₃` and the contradiction
  have hγmem : (h N * s N)⁻¹ * (g N * s N) ∈ Γ3 := by
    refine QuotientGroup.eq.mp ?_
    have e1 : mkX (h N * s N) = h N • x N := by
      rw [← hsx N]; exact Lemmas.mkX_mul (h N) (s N)
    have e2 : mkX (g N * s N) = g N • x N := by
      rw [← hsx N]; exact Lemmas.mkX_mul (g N) (s N)
    change mkX (h N * s N) = mkX (g N * s N)
    rw [e1, e2, hgh N]
  have hγ1 : (h N * s N)⁻¹ * (g N * s N) = 1 := gamma3_half _ hγmem hbound
  have hgn : g N = h N := by
    have h2 : g N * s N = h N * s N := by
      have h3 := congrArg (fun z => (h N * s N) * z) hγ1
      rwa [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at h3
    exact mul_right_cancel h2
  exact hne N hgn

end Work.EKLComp
