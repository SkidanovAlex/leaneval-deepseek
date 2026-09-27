import Mathlib
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLNonExc.MatrixFacts

/-!
# EKL Lemma 4.2 / ROUTE_LEAD L9.2: the `Bad` sets of "bad `Lset`-returns" are closed and null

`Bad a b c hab ℓ ℓu n ε` is the set of points of `Dinj (1/ℓu)` carrying, under the time-`n` map
`aPrime c n`, an `Lset hab`-displacement lying in the closed box `clBox (1/(2ℓ))` and with
`fmax ≥ ε`.  We prove the two facts needed by the C9 assembly:

* `Bad …` is **closed** — it is `Dinj (1/ℓu) ∩ BadCore …`, and `BadCore …`, the set of points
  carrying a witness in the compact box `clBox (1/(2ℓ))`, is the image of a closed subset of
  `X₃ × clBox (1/(2ℓ))` under the projection `Prod.fst`, which is a closed map because the box
  is compact (`isClosedMap_fst_of_compactSpace`);

* `μ (Bad …) = 0` whenever `3 * ℓu < ℓ` and `ε > 0`, for every `A`-invariant probability `μ`
  (EKL Lemma 4.2).  This is the Poincaré-recurrence argument of ROUTE_LEAD L9.2: the measure
  preserving map `T = (bconj a b c) • ·` returns to `Bad …` after some time `m`, and the two
  displacements `g`, `g'` of the two visits satisfy `g' = bconj^m * g * (bconj^m)⁻¹` by
  uniqueness of displacements at points of `Dinj (1/ℓu)`; but conjugating by `bconj^m` contracts
  the `fmax` entries by `e^{-m}`, while `g ∈ clBox (1/(2ℓ))` bounds `fmax g ≤ (2ℓ)⁻¹`, giving
  `ε ≤ e^{-m} (2ℓ)⁻¹ < ε` for `m` large.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.EKLNonExc

open MeasureTheory Filter Topology
open Work.EKLContract

noncomputable section

/-! ## The "exists a witness" part of `Bad` -/

/-- The second conjunct of `Bad`: the point carries an `Lset hab`-return under `aPrime c n` with
displacement in the closed box `clBox ((2ℓ)⁻¹)` and `fmax ≥ ε`. -/
def BadCore (a b c : Fin 3) (hab : a ≠ b) (ℓ n : ℕ) (ε : ℝ) : Set X3 :=
  {x | ∃ g : SL3, g ∈ clBox ((2 * (ℓ : ℝ))⁻¹) ∧ g ∈ Lset hab ∧
      aPrime c (n : ℝ) • x = g • x ∧ ε ≤ fmax a b c g}

/-- `Bad` is `Dinj (1/ℓu)` intersected with the witness set `BadCore`. -/
lemma bad_eq_Dinj_inter_BadCore (a b c : Fin 3) (hab : a ≠ b) (ℓ ℓu n : ℕ) (ε : ℝ) :
    Bad a b c hab ℓ ℓu n ε = Dinj ((ℓu:ℝ)⁻¹) ∩ BadCore a b c hab ℓ n ε := rfl

/-- `Lset hab`, the centraliser of `u_ab(1)`, is closed. -/
lemma isClosed_Lset {a b : Fin 3} (hab : a ≠ b) : IsClosed (Lset hab) := by
  rw [Lset]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

/-- `BadCore` is closed: it is the projection (along the compact second factor `clBox`) of the
closed set of witnesses `(x, g)`. -/
lemma isClosed_badCore (hcl : ∀ δ : ℝ, IsCompact (clBox δ))
    (a b c : Fin 3) (hab : a ≠ b) (ℓ n : ℕ) (ε : ℝ) :
    IsClosed (BadCore a b c hab ℓ n ε) := by
  haveI : CompactSpace (clBox ((2 * (ℓ : ℝ))⁻¹)) :=
    isCompact_iff_compactSpace.mp (hcl _)
  have hS : IsClosed {p : X3 × clBox ((2 * (ℓ : ℝ))⁻¹) |
      (p.2 : SL3) ∈ Lset hab ∧ aPrime c (n : ℝ) • p.1 = (p.2 : SL3) • p.1 ∧
        ε ≤ fmax a b c (p.2 : SL3)} := by
    have h1 : IsClosed {p : X3 × clBox ((2 * (ℓ : ℝ))⁻¹) | (p.2 : SL3) ∈ Lset hab} :=
      (isClosed_Lset hab).preimage (continuous_subtype_val.comp continuous_snd)
    have h2 : IsClosed {p : X3 × clBox ((2 * (ℓ : ℝ))⁻¹) |
        aPrime c (n : ℝ) • p.1 = (p.2 : SL3) • p.1} :=
      isClosed_eq ((continuous_const_smul (aPrime c (n:ℝ))).comp continuous_fst)
        (continuous_smul.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
    have h3 : IsClosed {p : X3 × clBox ((2 * (ℓ : ℝ))⁻¹) | ε ≤ fmax a b c (p.2 : SL3)} := by
      refine isClosed_le continuous_const ?_
      simp only [fmax]
      fun_prop
    simpa only [Set.ofPred_and] using h1.inter (h2.inter h3)
  have himg : Prod.fst '' {p : X3 × clBox ((2 * (ℓ : ℝ))⁻¹) |
      (p.2 : SL3) ∈ Lset hab ∧ aPrime c (n : ℝ) • p.1 = (p.2 : SL3) • p.1 ∧
        ε ≤ fmax a b c (p.2 : SL3)} = BadCore a b c hab ℓ n ε := by
    ext x; constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, p.2.2, hp.1, hp.2.1, hp.2.2⟩
    · rintro ⟨g, hgcl, hgL, heq, hf⟩
      exact ⟨(x, ⟨g, hgcl⟩), ⟨hgL, heq, hf⟩, rfl⟩
  rw [← himg]
  exact isClosedMap_fst_of_compactSpace _ hS

/-- `Bad …` is closed. -/
lemma bad_isClosed (hDinj : ∀ δ : ℝ, IsClosed (Dinj δ)) (hcl : ∀ δ : ℝ, IsCompact (clBox δ))
    (a b c : Fin 3) (hab : a ≠ b) (ℓ ℓu n : ℕ) (ε : ℝ) :
    IsClosed (Bad a b c hab ℓ ℓu n ε) := by
  rw [bad_eq_Dinj_inter_BadCore]
  exact (hDinj _).inter (isClosed_badCore hcl a b c hab ℓ n ε)

/-! ## Auxiliary estimates -/

/-- The `m`-fold iterate of the action of `g` is the action of `g ^ m`. -/
lemma iterate_smul_eq (g : SL3) (m : ℕ) (y : X3) :
    (fun x : X3 => g • x)^[m] y = g ^ m • y := by
  induction m with
  | zero => rw [pow_zero, Function.iterate_zero_apply, one_smul]
  | succ k ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']

/-- `fmax` is bounded by the box radius on the closed box. -/
lemma fmax_le_of_mem_clBox {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {g : SL3} {δ : ℝ} (hg : g ∈ clBox δ) : fmax a b c g ≤ δ := by
  have h1 : |g a b| ≤ δ := by
    have h := hg a b
    rwa [Matrix.one_apply, if_neg hab, sub_zero] at h
  have h2 : |g a c| ≤ δ := by
    have h := hg a c
    rwa [Matrix.one_apply, if_neg hac, sub_zero] at h
  have h3 : |g c b| ≤ δ := by
    have h := hg c b
    rwa [Matrix.one_apply, if_neg hcb, sub_zero] at h
  simp only [fmax]
  exact max_le (max_le h1 h2) h3

/-- For every `c > 0` and `ε > 0` there is `M` with `e^{-M} c < ε`. -/
lemma exists_exp_neg_mul_lt {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ M : ℕ, Real.exp (-(M:ℝ)) * c < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (c / ε) 1)
  refine ⟨N, ?_⟩
  have hN1 : (1:ℝ) < (N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNc : c / ε < (N:ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hexp : Real.exp (-(N:ℝ)) ≤ ((N:ℝ) + 1)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by linarith)]
    exact Real.add_one_le_exp (N:ℝ)
  calc Real.exp (-(N:ℝ)) * c ≤ ((N:ℝ) + 1)⁻¹ * c :=
        mul_le_mul_of_nonneg_right hexp (le_of_lt hc)
    _ = c / ((N:ℝ) + 1) := by rw [div_eq_inv_mul]
    _ < ε := by
        rw [div_lt_iff₀ (by linarith)]
        have h2 : c < ε * (N:ℝ) := by
          rw [div_lt_iff₀ hε] at hNc; linarith
        nlinarith [h2, hε]

/-- The key commutation: the actions of `aPrime c n` and of `bconj a b c ^ m` commute, so the
`bconj^m`-conjugate of the displacement `g` of a return `aPrime c n • y = g • y` is again a
displacement of the return `aPrime c n • (bconj^m • y)`. -/
lemma key_identity (a b c : Fin 3) (n m : ℕ) (g : SL3) (y : X3)
    (hgy : aPrime c (n:ℝ) • y = g • y) :
    aPrime c (n:ℝ) • ((bconj a b c ^ m) • y) =
      (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) • ((bconj a b c ^ m) • y) := by
  have hcomm : aPrime c (n:ℝ) * bconj a b c ^ m = bconj a b c ^ m * aPrime c (n:ℝ) :=
    ((Commute.pow_left (show Commute (bconj a b c) (aPrime c (n:ℝ)) from
      aPrime_commute_bconj a b c (n:ℝ))) m).eq.symm
  calc aPrime c (n:ℝ) • ((bconj a b c ^ m) • y)
      = (aPrime c (n:ℝ) * bconj a b c ^ m) • y := (mul_smul _ _ _).symm
    _ = (bconj a b c ^ m * aPrime c (n:ℝ)) • y := by rw [hcomm]
    _ = (bconj a b c ^ m) • (aPrime c (n:ℝ) • y) := mul_smul _ _ _
    _ = (bconj a b c ^ m) • (g • y) := by rw [hgy]
    _ = (bconj a b c ^ m * g) • y := (mul_smul _ _ _).symm
    _ = ((bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) * bconj a b c ^ m) • y := by
        rw [show (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) * bconj a b c ^ m
              = bconj a b c ^ m * g by group]
    _ = (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) • ((bconj a b c ^ m) • y) :=
        mul_smul _ _ _

/-! ## The nullity of `Bad` -/

/-- EKL Lemma 4.2: `Bad` is `μ`-null for every `A`-invariant probability `μ`, provided
`3 * ℓu < ℓ` and `ε > 0`. -/
lemma bad_null {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hBadClosed : ∀ (ℓ ℓu n : ℕ) (ε : ℝ), IsClosed (Bad a b c hab ℓ ℓu n ε))
    (μ : Measure X3) [IsProbabilityMeasure μ] (hμ : IsAInvariant μ)
    {ℓ ℓu n : ℕ} {ε : ℝ} (hℓu : 0 < ℓu) (hℓ : 3 * ℓu < ℓ) (hε : 0 < ε) :
    μ (Bad a b c hab ℓ ℓu n ε) = 0 := by
  -- the measure preserving map whose orbit returns to `Bad`
  have hT : MeasurePreserving (fun x : X3 => bconj a b c • x) μ μ := hμ (uvec a b c)
  have hcons : Conservative (fun x : X3 => bconj a b c • x) μ := hT.conservative
  have hℓpos : (0:ℝ) < (ℓ:ℝ) := by
    have : (0:ℝ) < (ℓu:ℝ) := by exact_mod_cast hℓu
    have h3 : (3:ℝ) * (ℓu:ℝ) < (ℓ:ℝ) := by exact_mod_cast hℓ
    linarith
  have hcpos : 0 < (2 * (ℓ : ℝ))⁻¹ := by positivity
  -- a time large enough to force the contradiction
  obtain ⟨M, hM⟩ := exists_exp_neg_mul_lt hcpos hε
  by_contra hne
  have hrec := hcons.measure_mem_forall_ge_image_notMem_eq_zero
      (hBadClosed ℓ ℓu n ε).measurableSet.nullMeasurableSet M
  -- Poincaré recurrence: some point of `Bad` returns to `Bad` after time `≥ M`
  have hex : ∃ y ∈ Bad a b c hab ℓ ℓu n ε, ∃ m : ℕ, M ≤ m ∧
      (fun x : X3 => bconj a b c • x)^[m] y ∈ Bad a b c hab ℓ ℓu n ε := by
    by_contra hcon
    push Not at hcon
    have hsub : Bad a b c hab ℓ ℓu n ε ⊆ {x : X3 | x ∈ Bad a b c hab ℓ ℓu n ε ∧
        ∀ m : ℕ, M ≤ m → (fun x : X3 => bconj a b c • x)^[m] x ∉ Bad a b c hab ℓ ℓu n ε} :=
      fun x hx => ⟨hx, fun m hm => hcon x hx m hm⟩
    have hzero : μ {x : X3 | x ∈ Bad a b c hab ℓ ℓu n ε ∧
        ∀ m : ℕ, M ≤ m → (fun x : X3 => bconj a b c • x)^[m] x ∉ Bad a b c hab ℓ ℓu n ε} = 0 :=
      hrec
    exact hne (le_antisymm (hzero ▸ measure_mono hsub) zero_le)
  obtain ⟨y, hy, m, hmM, hmy⟩ := hex
  obtain ⟨hyD, g, hgcl, hgL, hgy, hgf⟩ := hy
  obtain ⟨hmD, g', hg'cl, hg'L, hg'y, hg'f⟩ := hmy
  have hTy : (fun x : X3 => bconj a b c • x)^[m] y = bconj a b c ^ m • y :=
    iterate_smul_eq _ _ _
  rw [hTy] at hmD hg'y
  -- the two displacements both lie in `V (1/ℓu)`, where displacements are unique
  have hℓu' : (0:ℝ) < (ℓu:ℝ) := by exact_mod_cast hℓu
  have hδlt : (2 * (ℓ : ℝ))⁻¹ < ((ℓu : ℝ))⁻¹ := by
    have h3 : (3:ℝ) * (ℓu:ℝ) < (ℓ:ℝ) := by exact_mod_cast hℓ
    exact (inv_lt_inv₀ (by linarith : (0:ℝ) < 2 * (ℓ:ℝ)) hℓu').mpr (by linarith)
  have hg'V : g' ∈ V ((ℓu:ℝ)⁻¹) := fun i j => lt_of_le_of_lt (hg'cl i j) hδlt
  have hg''cl : bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹ ∈ clBox ((2 * (ℓ : ℝ))⁻¹) :=
    conj_mem_clBox hab hac hcb m (le_of_lt hcpos) hgL hgcl
  have hg''V : bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹ ∈ V ((ℓu:ℝ)⁻¹) :=
    fun i j => lt_of_le_of_lt (hg''cl i j) hδlt
  have heq : g' • (bconj a b c ^ m • y) =
      (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) • (bconj a b c ^ m • y) :=
    hg'y.symm.trans (key_identity a b c n m g y hgy)
  have huniq2 : g' = bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹ :=
    hmD g' _ hg'V hg''V heq
  -- `fmax` of the return is contractible by `e^{-m}`, and bounded by `(2ℓ)⁻¹`
  have h1 : ε ≤ fmax a b c (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) := by
    rw [← huniq2]; exact hg'f
  have h2 : fmax a b c (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) ≤
      Real.exp (-(m:ℝ)) * fmax a b c g := fmax_conj_le hab hac hcb m hgL
  have h3 : fmax a b c g ≤ (2 * (ℓ:ℝ))⁻¹ := fmax_le_of_mem_clBox hab hac hcb hgcl
  have h4 : Real.exp (-(m:ℝ)) ≤ Real.exp (-(M:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hmM' : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast hmM
    linarith
  have h5 : Real.exp (-(m:ℝ)) * (2*(ℓ:ℝ))⁻¹ ≤ Real.exp (-(M:ℝ)) * (2*(ℓ:ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_right h4 (le_of_lt hcpos)
  have h6 : Real.exp (-(m:ℝ)) * fmax a b c g ≤ Real.exp (-(m:ℝ)) * (2*(ℓ:ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  exact absurd (lt_of_le_of_lt (le_trans h1 (le_trans h2 (le_trans h6 h5))) hM) (lt_irrefl _)

end

theorem BadNull (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : Work.EKLContract.IsAInvariant μ)
    (hDinj : ∀ δ : ℝ, IsClosed (Work.EKLNonExc.Dinj δ))
    (hcl : ∀ δ : ℝ, IsCompact (Work.EKLNonExc.clBox δ)) :
    (∀ (ℓ ℓu n : ℕ) (ε : ℝ), IsClosed (Work.EKLNonExc.Bad a b c hab ℓ ℓu n ε)) ∧
    (∀ (ℓ ℓu n : ℕ) (ε : ℝ), 0 < ℓu → 3 * ℓu < ℓ → 0 < ε →
        μ (Work.EKLNonExc.Bad a b c hab ℓ ℓu n ε) = 0) := by
  have hclosed := bad_isClosed hDinj hcl a b c hab
  exact ⟨fun ℓ ℓu n ε => hclosed ℓ ℓu n ε,
    fun ℓ ℓu n ε hℓu hℓ hε =>
      bad_null hab hac hcb hclosed μ hμ hℓu hℓ hε⟩

end Work.EKLNonExc
