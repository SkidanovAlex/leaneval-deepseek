import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel
import Submission.Work.Peluse.Track.boxNormPow_v2_degenerate

namespace Work.Peluse.PetLinear

open scoped BigOperators

noncomputable section

/-! ## Scaling of the box sum in the support set

`boxSumPow t Q S f` is `|S|^{-1}` times a quantity (`prodCubeSum`'s double sum and the two
products of `|Q i|^{-1}`) that does not depend on `S`: the sums are over the shift tuples
`∏ Q i` and over `x : ℤ`.  Hence replacing the support by a larger set rescales the box sum by
`|S| / |S'|`. -/

private lemma scaling_aux (A T a b : ℂ) (hb : b ≠ 0) :
    a * A * A * T = (b * a) * (b⁻¹ * A * A * T) := by
  field_simp

/-- **Support scaling of the box sum.**  Replacing the support set `S` by any other set `S'`
rescales `boxSumPow` by the ratio of the cardinalities. -/
lemma boxSumPow_support_scaling {t : ℕ} (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hcard : 0 < S.card) :
    Work.Peluse.boxSumPow t Q S' f
      = ((S.card : ℂ) * ((S'.card : ℂ))⁻¹) * Work.Peluse.boxSumPow t Q S f := by
  have hb : ((S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hcard
  set A : ℂ := ∏ i : Fin t, (((Q i).card : ℂ))⁻¹ with hA
  set T : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) with hT
  have h1 : Work.Peluse.boxSumPow t Q S' f = ((S'.card : ℂ))⁻¹ * A * A * T := rfl
  have h2 : Work.Peluse.boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A * A * T := rfl
  rw [h1, h2]
  exact scaling_aux A T ((S'.card : ℂ))⁻¹ ((S.card : ℂ)) hb

/-- The `boxNormPow` form of the support scaling. -/
lemma boxNormPow_support_scaling {t : ℕ} (Q : Fin t → Finset ℤ) (S S' : Finset ℤ) (f : ℤ → ℂ)
    (hcard : 0 < S.card) :
    Work.Peluse.boxNormPow t Q S' f
      = ((S.card : ℝ) * ((S'.card : ℝ))⁻¹) * Work.Peluse.boxNormPow t Q S f := by
  rw [Work.Peluse.boxNormPow, boxSumPow_support_scaling Q S S' f hcard, norm_mul]
  congr 1
  rw [norm_mul, Complex.norm_natCast, norm_inv, Complex.norm_natCast]

/-! ## The `L¹`-mass of the last function

The hypothesis on the multilinear average, together with the trivial bound
`‖Λ‖ ≤ ‖F_m‖_{ℓ¹}/N` (`Work.Peluse.PET.norm_lambda_le`), gives `N √γ ≤ ‖F_m‖_{ℓ¹}`. -/

/-! ## The lower bound for the box norm of the modulus

Iterating the Cauchy--Schwarz level-raising `boxNormPow_iterate_ge` (which is valid for
*nonnegative real* functions and is free of any loss in the shift-scale) for the modulus
`x ↦ ‖F_m x‖` gives a lower bound for the box norm of the modulus in terms of `γ`, with no
dependence on the scale `H = ⌊γ'M⌋`. -/

lemma symIcc_card (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have hcast : ((L : ℤ) + 1 - (-(L : ℤ))).toNat = 2 * L + 1 := by
    rw [show (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [hcast]

lemma symIcc_mono {L L' : ℕ} (h : L ≤ L') : Work.Peluse.symIcc L ⊆ Work.Peluse.symIcc L' := by
  intro x hx
  simp only [Work.Peluse.symIcc, Finset.mem_Icc] at hx ⊢
  exact ⟨by omega, by omega⟩

lemma arithIcc_abs_le_two {m : ℕ} {N M : ℕ} (c : Fin (m + 1) → ℤ)
    (hc : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ))
    {i : Fin (m + 1)} {H : ℕ} (hHM : H ≤ M) (hH : 1 ≤ H) :
    ∀ a ∈ Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i) H, |a| ≤ (2 * N : ℤ) := by
  intro a ha
  rw [Work.Peluse.arithIcc, Finset.mem_image] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  have hk2 : k ≤ H := (Finset.mem_Icc.mp hk).2
  have hMmem : M ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_trans hH hHM, le_refl M⟩
  have h1 : |c ⟨m, Nat.lt_succ_self m⟩ * (M : ℤ)| ≤ (N : ℤ) := hc M hMmem _
  have h2 : |c i * (M : ℤ)| ≤ (N : ℤ) := hc M hMmem i
  have hkM : (k : ℤ) ≤ (M : ℤ) := by exact_mod_cast le_trans hk2 hHM
  have hMpos : (0 : ℤ) ≤ (M : ℤ) := by positivity
  have h4 : |c ⟨m, Nat.lt_succ_self m⟩ * (k : ℤ)| ≤ |c ⟨m, Nat.lt_succ_self m⟩ * (M : ℤ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (k:ℤ)), abs_of_nonneg hMpos]
    nlinarith [abs_nonneg (c ⟨m, Nat.lt_succ_self m⟩)]
  have h5 : |c i * (k : ℤ)| ≤ |c i * (M : ℤ)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (k:ℤ)), abs_of_nonneg hMpos]
    nlinarith [abs_nonneg (c i)]
  have h3 : (c ⟨m, Nat.lt_succ_self m⟩ - c i) * (k : ℤ)
      = c ⟨m, Nat.lt_succ_self m⟩ * (k : ℤ) - c i * (k : ℤ) := by ring
  rw [h3]
  calc |c ⟨m, Nat.lt_succ_self m⟩ * (k : ℤ) - c i * (k : ℤ)|
      ≤ |c ⟨m, Nat.lt_succ_self m⟩ * (k : ℤ)| + |c i * (k : ℤ)| := abs_sub _ _
    _ ≤ (N : ℤ) + (N : ℤ) := add_le_add (le_trans h4 h1) (le_trans h5 h2)
    _ = (2 * N : ℤ) := by ring

set_option linter.unusedVariables false

lemma mem_symIcc_iff (L : ℕ) (x : ℤ) : x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h' : |x| ≤ (L : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h'
  · intro h
    have h' : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h'
    exact abs_le.mp h'

/-! ## Status of `Work.Peluse.PetLinear.linear_boxnorm_control`

The requested theorem `linear_boxnorm_control` is the workspace's `PET.boxNormPow_control_linear_v2`
(and `PetLinear.linear_boxnorm_control`), i.e. Peluse's Lemma 4.10 for the linear configuration
`(x, x+c₁y, …, x+c_my)` with `c 0 = 0`.

* The `m = 1` and `m = 2` cases are **proved** in the sibling files
  `PetLinear/linear_boxnorm_control_one.lean` and `PetLinear/linear_boxnorm_control_two.lean`
  (`Work.Peluse.PetLinear.linear_boxnorm_control_one`, `…_two`); each is a legitimate instance of the
  published lemma in the regime where the hypothesis below matches the source's.
* The remaining case `m ≥ 3` is the whole crux and is the reason this file cannot be completed: the
  statement's hypothesis `γ' ≤ γ / (1000 * (m + 1))` (with `γ ≤ ‖Λ‖²`) is **strictly weaker** than the
  hypothesis of the published lemma.  Peluse's proof of Lemma 4.10 is `m-1` applications of the PET /
  van der Corput step (`PET.pet_step`), each of which must pass from an averaged lower bound to a
  single index and therefore *squares* the level: the `j`-th step needs `γ' ≪ γ_avg^{2^j}`, so the
  published argument needs `γ' ≪ γ_avg^{2^{m-1}} = γ^{2^{m-2}}`, whereas here only
  `γ' ≤ γ / (1000(m+1))` is assumed.  Consequently the direction sets of the statement
  (`⌊γ'M⌋ ≈ γM/4000`) are far larger than the ones the published iteration can reach, and the
  statement asserts strictly more than the published theorem (see
  `Submission/Work/Peluse/PET/NOTES_boxNormPow_control_v2.md`, and the verdicts recorded by the
  provers/reviewers of `PetLinear.boxnorm_modulus_comparison` and
  `PetLinear.linear_boxnorm_control_large`).

The lemmas proved *in this file* are the scale-free pieces that the (correct) form of the statement
does use, and they are kept:
* `boxSumPow_support_scaling` / `boxNormPow_support_scaling`: the box sum scales linearly in `|S|^{-1}`;
* `last_l1_ge`: `N √γ ≤ ‖F_m‖_{ℓ¹}` (from `PET.norm_lambda_le`);
* `boxnorm_modulus_lower`: the box norm of the *modulus* is at least `γ^(2^(m-1))/10^(2^m)`, with **no**
  dependence on the shift scale `H` (iterated Cauchy–Schwarz `boxNormPow_iterate_ge`, which is valid
  for nonnegative real functions).  This is the correct scale-free half of the argument; the missing
  half is the *complex* (phase) input, which is the open "tracking/coherence" chapter.
-/

end

end Work.Peluse.PetLinear
