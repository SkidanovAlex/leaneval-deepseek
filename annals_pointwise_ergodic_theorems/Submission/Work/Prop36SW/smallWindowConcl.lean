import Mathlib
import Submission.Work.Prop36SW.boxNorm_zero_dir_le
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The small-window conclusion for the family average

The lemma `Work.Prop36SW.smallWindowConcl` is the "small window" half of the passage from the
family average `D.famAvg d H c N f` (an average of level-`|I_{d-1}|` box norms at the parameter
box) to the uniformity-norm power at the *shortest possible* window `κ[1] = {κ}`.

## The mathematics

Everything rests on two facts about a singleton direction family.

* **The uniformity norm at a singleton is the normalised `L^{2^s}`-mass.**  For `1 ≤ s` and `f`
  supported in `symIcc N`,

  `‖f‖^{2^s}_{U^s_{{κ}}(symIcc N)} = |symIcc N|⁻¹ ∑_{x∈symIcc N} ‖f x‖^{2^s}`,

  independent of `κ` (`Work.Peluse.Ulower.uNormPow_singleton_symIcc`).  (The cube average at a
  singleton direction set collapses to the `2^s`-th moment, and the `x`-sum is translation
  invariant.)

* **A box norm is dominated by the `L^{2^t}`-mass** (`Work.Prop36SW.boxNormPow_le_normAvgPow`),
  hence — by the power mean (Jensen) on the probability space `symIcc N` and `‖f‖ ≤ 1` — by the
  mass at the larger exponent `2^s` (for `t ≤ s`).

So: the family average is at least `η`, hence some parameter `a` of the box has
`η ≤ ‖f‖_{□^t_{Q(a)}(symIcc N)}`; `Work.Prop36SW.boxNorm_zero_dir_le` turns that single box-norm
bound into `η ≤ ‖f‖_{U^s_{{0}}(symIcc N)}`, and the two singleton identities identify that with
`η ≤ (uNormPow s (arithIcc κ 1) (symIcc N) f)^{1/2^s}`.  Raising to the `2^s`-th power and using
`K ≥ 2^s`, `0 < η ≤ 1` and `1 ≤ A` gives the claim.
-/

open scoped BigOperators

namespace Work.Prop36SW

open Work.Peluse

/-- If a finite family of nonnegative reals has average at least `η`, then one of its members is
at least `η`. -/
private lemma exists_mem_le_of_le_inv_card_sum {ι : Type} (A : Finset ι) (g : ι → ℝ) (η : ℝ)
    (hne : A.Nonempty) (h : η ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, g a) :
    ∃ a ∈ A, η ≤ g a := by
  by_contra hcon
  push_neg at hcon
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hlt : ∑ a ∈ A, g a < ∑ a ∈ A, η := by
    refine Finset.sum_lt_sum (fun a ha => (hcon a ha).le) ?_
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, hcon a ha⟩
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have h2 : (A.card : ℝ)⁻¹ * ∑ a ∈ A, g a < η := by
    have h3 : (A.card : ℝ)⁻¹ * ∑ a ∈ A, g a < (A.card : ℝ)⁻¹ * ((A.card : ℝ) * η) :=
      mul_lt_mul_of_pos_left hlt (inv_pos.mpr hcard)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul] at h3
  linarith

theorem smallWindowConcl (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ)
    (N H : ℕ) (f : ℤ → ℂ) (η : ℝ) (κ : ℤ) (s K : ℕ) (A : ℝ)
    (hd : 1 ≤ d) (hN : 1 ≤ N) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsu : Work.Peluse.SupportIn f N)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hfam : η ≤ D.famAvg d H c N f)
    (hs : Fintype.card (D.I (d - 1)) ≤ s) (hs2 : 2 ≤ s)
    (hK : 2 ^ s ≤ K) (hA : 1 ≤ A) :
    η ^ K ≤ A * Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ 1) (Work.Peluse.symIcc N) f
:= by
  have hηnn : 0 ≤ η := hη0.le
  have hs1 : 1 ≤ s := by omega
  have hzero : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 :=
    fun x hx => hsu x (Work.Peluse.Ulower.lt_natAbs_of_notMem_symIcc hx)
  -- the parameter box is non-empty (otherwise the family average vanishes)
  have hne : (D.parBox d H).Nonempty := by
    by_contra hemp
    have h0 : D.famAvg d H c N f = 0 := by
      have hemp' : D.parBox d H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
      simp [Work.Peluse.UControl.IdxDatum.famAvg, hemp']
    rw [h0] at hfam
    linarith
  -- some parameter attains the family average up to `η`
  obtain ⟨a, ha, hage⟩ := exists_mem_le_of_le_inv_card_sum (D.parBox d H)
    (fun a => D.famNorm d H c N a f) η hne hfam
  -- that single level-`|I_{d-1}|` box norm is at least `η`
  have hbox : η ≤ Work.Peluse.boxNorm (Fintype.card (D.I (d - 1)))
      (fun i : Fin (Fintype.card (D.I (d - 1))) =>
        Work.Peluse.arithIcc
          (D.dir d c (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm i) (D.pad d a)) H)
      (Work.Peluse.symIcc N) f := by
    simpa only [Work.Peluse.UControl.IdxDatum.famNorm] using hage
  -- the degenerate-direction concatenation at the singleton `0[1] = {0}`
  have hδ : η ≤ Work.Peluse.uNorm s (Work.Peluse.arithIcc 0 1) (Work.Peluse.symIcc N) f :=
    boxNorm_zero_dir_le hs1 hs N H 1
      (fun i => D.dir d c (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm i) (D.pad d a))
      η f le_rfl hsu hf hη0 hbox
  -- raise the conclusion to the `2 ^ s`-th power
  have hηpow : η ^ (2 ^ s) ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc 0 1)
      (Work.Peluse.symIcc N) f := by
    have h := hδ
    rw [Work.Peluse.uNorm] at h
    have hexp : (1 : ℝ) / (2 : ℝ) ^ s = (((2 ^ s : ℕ) : ℝ))⁻¹ := by
      rw [one_div, eq_comm]; norm_num
    rw [hexp] at h
    have hu : (0 : ℝ) ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc 0 1)
        (Work.Peluse.symIcc N) f := by
      rw [Work.Peluse.uNormPow, Work.Peluse.boxNormPow]
      exact norm_nonneg _
    have h2 := pow_le_pow_left₀ hηnn h (2 ^ s)
    rwa [Real.rpow_inv_natCast_pow hu (pow_ne_zero s (by norm_num : (2 : ℕ) ≠ 0))] at h2
  -- the singleton direction sets `{0}` and `{κ}` carry the same norm
  have hsing : Work.Peluse.uNormPow s (Work.Peluse.arithIcc 0 1) (Work.Peluse.symIcc N) f
      = Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ 1) (Work.Peluse.symIcc N) f := by
    have h1 : Work.Peluse.uNormPow s ({0} : Finset ℤ) (Work.Peluse.symIcc N) f
        = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s) :=
      Work.Peluse.Ulower.uNormPow_singleton_symIcc hs1 hzero
    have h2 : Work.Peluse.uNormPow s ({κ} : Finset ℤ) (Work.Peluse.symIcc N) f
        = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
          * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s) :=
      Work.Peluse.Ulower.uNormPow_singleton_symIcc hs1 hzero
    rw [Work.Peluse.Ulower.arithIcc_one_eq_singleton 0,
      Work.Peluse.Ulower.arithIcc_one_eq_singleton κ, h1, h2]
  have hfin : (0 : ℝ) ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ 1)
      (Work.Peluse.symIcc N) f := by
    rw [Work.Peluse.uNormPow, Work.Peluse.boxNormPow]
    exact norm_nonneg _
  calc η ^ K ≤ η ^ (2 ^ s) := pow_le_pow_of_le_one hηnn hη1 hK
    _ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ 1) (Work.Peluse.symIcc N) f := by
        rw [← hsing]; exact hηpow
    _ ≤ A * Work.Peluse.uNormPow s (Work.Peluse.arithIcc κ 1) (Work.Peluse.symIcc N) f :=
        le_mul_of_one_le_left hfin hA

end Work.Prop36SW
