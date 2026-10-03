import Mathlib
import Submission.Work.Peluse.Prop36SW.extDatum
import Submission.Work.Prop36SW.meanSq_le_boxNormPow_one
import Submission.Work.Prop36SW.boxNorm_zero_eq_mean
import Submission.Work.Peluse.Prop36SW.nodeBody

/-!
# The degenerate branch of `Work.Peluse.prop36SW_of_ladderA`

If `Fintype.card (D.I (d-1)) ≤ 1` (i.e. `D.S (d-1)` has at most one slot) then the family
`I_{d-1}` of `D.famNorm` has at most one member, and the §5 chain's entry — which needs the
level-`1` window enlargement, false at level `1` — is unavailable.

The remedy (`Submission/Work/Peluse/Prop36SW/extDatum.lean`) is to adjoin two fresh slots at every
level, `extDatum D`, which has `Fintype.card ((extDatum D).I j) ≥ 3` and therefore admits the chain
(`Work.Peluse.prop36SW_body`).  The old datum embeds through `Sum.inl`, the direction polynomials
agree, and the family average of the extension dominates that of `D`: for each extended parameter
the level-`S` box norm dominates the level-`1` box norm at one of its directions
(`Work.Prop36SW.boxNorm_le_levelRaise_first` plus the ambient bookkeeping
`Work.Peluse.Ulower.boxNormPow_eq_mul_card`), and the parameter boxes factor as
`D.parBox = (D'.parBox) × (fresh box)` so that the extra averaging cancels the extra cardinality.

## The structure of the argument

1. `boxNorm_le_levelRaise_half`: the level raising with the explicit constant `1/2`.
2. `famAvg_le_extFamAvg`: `C · D.famAvg ≤ (extDatum D).famAvg` with an `A₀`-dependent,
   data-independent constant `C ∈ (0,1]`.
3. `prop36SW_degenerate`: the branch, by applying `prop36SW_body` to `extDatum D` and rescaling
   `η ↦ Cη`, `A ↦ A'/C^{K'}` (which leaves the window `⌊max 1 (η^K δ'^d M^d / A)⌋` unchanged).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl

/-! ## The direction families -/

/-- The level-`(d-1)` direction family of the extended datum. -/
def famDirExt (D : IdxDatum) (d H : ℕ) (c : ℤ) (β : (extDatum D).Idx d) :
    Fin (Fintype.card ((extDatum D).I (d - 1))) → Finset ℤ :=
  fun i => arithIcc ((extDatum D).dir d c (d - 1)
    ((Fintype.equivFin ((extDatum D).I (d - 1))).symm i) ((extDatum D).pad d β)) H

/-- The level-`(d-1)` direction family of `D`. -/
def famDirOld (D : IdxDatum) (d H : ℕ) (c : ℤ) (a : D.Idx d) :
    Fin (Fintype.card (D.I (d - 1))) → Finset ℤ :=
  fun i => arithIcc (D.dir d c (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm i) (D.pad d a)) H

lemma famNorm_eq_boxNorm (D : IdxDatum) (d H N : ℕ) (c : ℤ) (a : D.Idx d) (f : ℤ → ℂ) :
    D.famNorm d H c N a f = boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c a)
      (symIcc N) f := rfl

lemma extFamNorm_eq_boxNorm (D : IdxDatum) (d H N : ℕ) (c : ℤ) (β : (extDatum D).Idx d)
    (f : ℤ → ℂ) :
    (extDatum D).famNorm d H c N β f =
      boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β) (symIcc N) f := rfl

/-! ## The ambient ratio for box norms -/

/-- The box norm depends on the ambient window only through the `(2^t)`-th root of the cardinality
ratio (`Work.Peluse.Ulower.boxNormPow_eq_mul_card`). -/
theorem boxNorm_symIcc_ratio (t : ℕ) (Q : Fin t → Finset ℤ) {N N' : ℕ}
    (hN' : (symIcc N').Nonempty) (f : ℤ → ℂ) :
    boxNorm t Q (symIcc N) f
      = (((symIcc N').card : ℝ) / ((symIcc N).card : ℝ)) ^ ((1 : ℝ) / (2 : ℝ) ^ t)
        * boxNorm t Q (symIcc N') f := by
  rw [boxNorm, boxNorm, Work.Peluse.Ulower.boxNormPow_eq_mul_card t Q (symIcc N) (symIcc N') f hN']
  exact Real.mul_rpow (by positivity) (norm_nonneg _)


/-- Support in a larger window from support in a smaller one. -/
lemma supportIn_mono_of_le {f : ℤ → ℂ} {N N' : ℕ} (h : N ≤ N') (hf : SupportIn f N) :
    SupportIn f N' :=
  fun x hx => hf x (lt_of_le_of_lt (by exact_mod_cast h) hx)

/-- `SupportIn` as vanishing off the symmetric window. -/
lemma supportIn_iff_forall {N : ℕ} {f : ℤ → ℂ} :
    SupportIn f N ↔ ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
  constructor
  · intro hf x hx
    refine hf x ?_
    have h : ((N : ℕ) : ℤ) < (x.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact not_le.mp fun hle => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hle)
    exact_mod_cast h
  · intro hf x hx
    refine hf x ?_
    intro hmem
    rw [Work.Peluse.PET.mem_symIcc_iff_abs] at hmem
    have h : (N : ℤ) < |x| := by
      rw [← Int.natCast_natAbs]; exact_mod_cast hx
    omega


/-- The level-`(d-1)` direction of the extended datum, at the index taken by the `equivFin`
enumeration of an old index, agrees with the old direction. -/
lemma extFamDir_eq_oldFamDir (D : IdxDatum) (d H : ℕ) (c : ℤ) (β : (extDatum D).Idx d)
    (ω : D.I (d - 1)) :
    famDirExt D d H c β (Fintype.equivFin ((extDatum D).I (d - 1)) (extIdx D (d - 1) ω))
      = arithIcc (D.dir d c (d - 1) ω (D.pad d (oldPart D β))) H := by
  rw [famDirExt]
  congr 1
  rw [Equiv.symm_apply_apply]
  exact dir_extDatum D d c (d - 1) ω (D.pad d (oldPart D β)) ((extDatum D).pad d β)
    (fun j s => by
      rw [IdxDatum.pad, IdxDatum.pad]
      by_cases h : j < d
      · simp only [dif_pos h]; rfl
      · simp only [dif_neg h])


/-- The box-norm power is invariant under transporting the index type. -/
lemma boxNormPow_eq_of_eq {t t' : ℕ} (h : t = t') (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    boxNormPow t Q S f = boxNormPow t' (fun i : Fin t' => Q (Fin.cast h.symm i)) S f := by
  subst h
  simp

/-- The box norm is invariant under transporting the index type. -/
lemma boxNorm_eq_of_eq {t t' : ℕ} (h : t = t') (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    boxNorm t Q S f = boxNorm t' (fun i : Fin t' => Q (Fin.cast h.symm i)) S f := by
  subst h
  simp [boxNorm]

/-- At a single direction, the box norm only sees the value of the family. -/
lemma boxNorm_one_eq_of_card_one {t : ℕ} (h : t = 1) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    boxNorm t Q S f = boxNorm 1 (fun _ : Fin 1 => Q (Fin.cast h.symm ⟨0, by omega⟩)) S f := by
  subst h
  congr 1
  funext i
  exact congrArg Q (Subsingleton.elim i ⟨0, by omega⟩)

/-- The final assembly of the pointwise comparison, given the level raise at `i₀` and the
comparison of `D.famNorm` with the level-one norm at `i₀`. -/
theorem extFamNorm_ge_aux (C₁ : ℝ) (hC₁pos : 0 < C₁) (D : IdxDatum) (d H N₁ : ℕ) (c : ℤ) (f : ℤ → ℂ)
    (β : (extDatum D).Idx d) (i₀ : Fin (Fintype.card ((extDatum D).I (d - 1))))
    (hi₀ : C₁ * boxNorm 1 (fun _ : Fin 1 => famDirExt D d H c β i₀) (symIcc N₁) f
      ≤ boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β) (symIcc N₁) f)
    (hle : D.famNorm d H c N₁ (oldPart D β) f
      ≤ Real.sqrt 2 * boxNorm 1 (fun _ : Fin 1 => famDirExt D d H c β i₀) (symIcc N₁) f) :
    (Real.sqrt 2)⁻¹ * C₁ * D.famNorm d H c N₁ (oldPart D β) f
      ≤ (extDatum D).famNorm d H c N₁ β f := by
  set A : ℝ := boxNorm 1 (fun _ : Fin 1 => famDirExt D d H c β i₀) (symIcc N₁) f with hA
  have hconst : (Real.sqrt 2)⁻¹ * C₁ * (Real.sqrt 2 * A) = C₁ * A := by
    have h2 : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = (1 : ℝ) :=
      inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0)
    calc (Real.sqrt 2)⁻¹ * C₁ * (Real.sqrt 2 * A)
        = ((Real.sqrt 2)⁻¹ * Real.sqrt 2) * (C₁ * A) := by ring
      _ = 1 * (C₁ * A) := by rw [h2]
      _ = C₁ * A := by ring
  calc (Real.sqrt 2)⁻¹ * C₁ * D.famNorm d H c N₁ (oldPart D β) f
      ≤ (Real.sqrt 2)⁻¹ * C₁ * (Real.sqrt 2 * A) := by
        rw [hA]
        exact mul_le_mul_of_nonneg_left hle
          (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)) hC₁pos.le)
    _ = C₁ * A := hconst
    _ ≤ boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β) (symIcc N₁) f := by
        rw [hA]; exact hi₀
    _ = (extDatum D).famNorm d H c N₁ β f := by rw [extFamNorm_eq_boxNorm]

/-- **The pointwise comparison at the inflated ambient** (the level-raise step): every extended
parameter satisfies the family-norm comparison with a constant independent of the data, once the
direction family fits inside the ambient. -/
theorem extFamNorm_ge_at (C₁ : ℝ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ (S : ℕ) (hS : 1 ≤ S) (Q : Fin S → Finset ℤ) {N : ℕ} (hN : 0 < N) {f : ℤ → ℂ}
      (hsup : ∀ x : ℤ, x ∉ symIcc N → f x = 0) (hbb : ∀ x : ℤ, ‖f x‖ ≤ 1)
      (hQ : ∀ i, (Q i).Nonempty) (hbdd : ∀ (i : Fin S) (z : ℤ), z ∈ Q i → |z| ≤ (N : ℤ))
      (i₀ : Fin S) (hQ₀ : (Q i₀).Nonempty),
      C₁ * boxNorm 1 (fun _ : Fin 1 => Q i₀) (symIcc N) f ≤ boxNorm S Q (symIcc N) f)
    (D : IdxDatum) (d : ℕ) (hd : 1 ≤ d) (c : ℤ) (H N₁ : ℕ) (f : ℤ → ℂ) (β : (extDatum D).Idx d)
    (hH : 1 ≤ H) (hN₁ : 0 < N₁) (hb1 : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hsu₁ : ∀ x : ℤ, x ∉ symIcc N₁ → f x = 0)
    (hfit : ∀ (i : Fin (Fintype.card ((extDatum D).I (d - 1)))) (z : ℤ),
      z ∈ famDirExt D d H c β i → |z| ≤ (N₁ : ℤ))
    (hβ : β ∈ (extDatum D).parBox d H)
    (hcard : Fintype.card (D.I (d - 1)) ≤ 1) :
    (Real.sqrt 2)⁻¹ * C₁ * D.famNorm d H c N₁ (oldPart D β) f
      ≤ (extDatum D).famNorm d H c N₁ β f := by
  classical
  set S' : ℕ := Fintype.card ((extDatum D).I (d - 1)) with hS'def
  have hS'1 : 1 ≤ S' := le_trans (by norm_num) (three_le_card_extI D (d - 1))
  have hQne : ∀ i : Fin S', (famDirExt D d H c β i).Nonempty := by
    intro i
    rw [famDirExt]
    exact ⟨_, Finset.mem_image.mpr ⟨1, by rw [Finset.mem_Icc]; omega, (mul_one _).symm⟩⟩
  by_cases h0 : Fintype.card (D.I (d - 1)) = 0
  · -- ## case B: `famNorm` is the mean
    refine extFamNorm_ge_aux C₁ hC₁pos D d H N₁ c f β ⟨0, by omega⟩ ?_ ?_
    · exact hC₁ S' hS'1 _ hN₁ hsu₁ hb1 hQne hfit _ (hQne _)
    · rw [famNorm_eq_boxNorm, boxNorm_eq_of_eq (Q := famDirOld D d H c (oldPart D β)) h0
        (S := symIcc N₁) (f := f)]
      rw [Work.Prop36SW.boxNorm_zero_eq_mean (symIcc N₁)
        (fun i : Fin 0 => famDirOld D d H c (oldPart D β) (Fin.cast h0.symm i)) f
        (Work.Peluse.FinSuppZ.of_supportIn ((supportIn_iff_forall).mpr hsu₁))]
      rw [tsum_eq_sum (s := symIcc N₁) (fun x hx => hsu₁ x hx)]
      have hdirit : famDirExt D d H c β (⟨0, by omega⟩ : Fin S')
          = arithIcc ((extDatum D).dir d c (d - 1)
              ((Fintype.equivFin ((extDatum D).I (d - 1))).symm ⟨0, by omega⟩)
              ((extDatum D).pad d β)) H := rfl
      have hme := Work.Prop36SW.meanSq_le_boxNormPow_one
        ((extDatum D).dir d c (d - 1) ((Fintype.equivFin ((extDatum D).I (d - 1))).symm ⟨0, by omega⟩)
          ((extDatum D).pad d β)) H N₁ f hH
        (hfit ⟨0, by omega⟩)
        ((supportIn_iff_forall).mpr hsu₁)
      have hu : uNormPow 1 (arithIcc ((extDatum D).dir d c (d - 1)
            ((Fintype.equivFin ((extDatum D).I (d - 1))).symm ⟨0, by omega⟩)
            ((extDatum D).pad d β)) H) (symIcc N₁) f
          = boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩) (symIcc N₁) f := by
        rw [hdirit]
        rfl
      rw [hu] at hme
      have hsqrt : boxNorm 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩) (symIcc N₁) f
          = Real.sqrt (boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩)
              (symIcc N₁) f) := by
        rw [boxNorm, Real.sqrt_eq_rpow]
        norm_num
      rw [hsqrt]
      have hsq : (‖(((symIcc N₁).card : ℂ))⁻¹ * ∑ x ∈ symIcc N₁, f x‖) ^ 2
          ≤ 2 * boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩) (symIcc N₁) f := by
        linarith [hme]
      have h2 : (0 : ℝ) ≤ ‖(((symIcc N₁).card : ℂ))⁻¹ * ∑ x ∈ symIcc N₁, f x‖ := norm_nonneg _
      have h4 : ‖(((symIcc N₁).card : ℂ))⁻¹ * ∑ x ∈ symIcc N₁, f x‖
          ≤ Real.sqrt (2 * boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩)
              (symIcc N₁) f) := by
        have hb : (0 : ℝ) ≤ 2 * boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩)
            (symIcc N₁) f := mul_nonneg (by norm_num) (by rw [boxNormPow]; exact norm_nonneg _)
        nlinarith [h2, hsq, Real.sq_sqrt hb, Real.sqrt_nonneg (2 * boxNormPow 1
          (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩) (symIcc N₁) f)]
      have h5 : Real.sqrt 2 * Real.sqrt (boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩)
            (symIcc N₁) f)
          = Real.sqrt (2 * boxNormPow 1 (fun _ : Fin 1 => famDirExt D d H c β ⟨0, by omega⟩)
              (symIcc N₁) f) := (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _).symm
      linarith [h4, h5]
  · -- ## case A: the direction identity
    have ht1 : Fintype.card (D.I (d - 1)) = 1 := by omega
    have hsub : ∀ a b : D.I (d - 1), a = b := Fintype.card_le_one_iff.mp (le_of_eq ht1)
    refine extFamNorm_ge_aux C₁ hC₁pos D d H N₁ c f β
      (Fintype.equivFin _ (extIdx D (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩))) ?_ ?_
    · exact hC₁ S' hS'1 _ hN₁ hsu₁ hb1 hQne hfit _ (hQne _)
    · rw [famNorm_eq_boxNorm, boxNorm_one_eq_of_card_one ht1 (famDirOld D d H c (oldPart D β))]
      have hdir : famDirExt D d H c β
            (Fintype.equivFin _ (extIdx D (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩)))
          = arithIcc (D.dir d c (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩)
              (D.pad d (oldPart D β))) H :=
        extFamDir_eq_oldFamDir D d H c β ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩)
      have h1 : boxNorm 1 (fun _ : Fin 1 => famDirExt D d H c β
              (Fintype.equivFin _ (extIdx D (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩))))
            (symIcc N₁) f
          = boxNorm 1 (fun _ : Fin 1 => arithIcc (D.dir d c (d - 1)
              ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩) (D.pad d (oldPart D β))) H)
            (symIcc N₁) f := by
        congr 1
        funext i
        exact hdir
      rw [h1]
      have hfam : famDirOld D d H c (oldPart D β) (Fin.cast ht1.symm ⟨0, by omega⟩)
          = arithIcc (D.dir d c (d - 1) ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩)
              (D.pad d (oldPart D β))) H := by
        rw [famDirOld]
        exact congrArg (fun ω => arithIcc (D.dir d c (d - 1) ω (D.pad d (oldPart D β))) H)
          (hsub _ _)
      rw [hfam]
      have hA0 : (0 : ℝ) ≤ boxNorm 1 (fun _ : Fin 1 => arithIcc (D.dir d c (d - 1)
            ((Fintype.equivFin (D.I (d - 1))).symm ⟨0, by omega⟩) (D.pad d (oldPart D β))) H)
          (symIcc N₁) f := by
        rw [boxNorm]; exact Real.rpow_nonneg (norm_nonneg _) _
      have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith [h2, hA0]

/-! ## The auxiliary arithmetic -/

/-- The level-`S` box norm dominates half of the level-`1` box norm at any one of its directions.
This is `Work.Prop36SW.boxNorm_le_levelRaise_first` with the constant fixed to `1/2`. -/
theorem boxNorm_le_levelRaise_half (S : ℕ) (hS : 1 ≤ S) (Q : Fin S → Finset ℤ)
    {N : ℕ} (hN : 0 < N) {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, x ∉ symIcc N → f x = 0)
    (hb1 : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hQ : ∀ i, (Q i).Nonempty)
    (hbdd : ∀ (i : Fin S) (z : ℤ), z ∈ Q i → |z| ≤ (N : ℤ))
    (i₀ : Fin S) (hQ₀ : (Q i₀).Nonempty) :
    (1 / 2) * boxNorm 1 (fun _ : Fin 1 => Q i₀) (symIcc N) f ≤ boxNorm S Q (symIcc N) f := by
  let e : Fin 1 ↪ Fin S := ⟨fun _ => i₀, fun a b _ => by ext; omega⟩
  have key := Work.Prop36SW.boxNormPow_le_of_inj (N := N) hN f hsup S 1 hS
    (fun _ : Fin 1 => Q i₀) Q e (fun _ => rfl) hQ (fun i z hz => hbdd i z hz)
  have h2 := Work.Prop36SW.boxNorm_le_of_boxNormPow_le hS (fun _ : Fin 1 => Q i₀) Q (symIcc N) f key
  linarith [h2]

/-- The cardinality of the symmetric window. -/
private lemma card_symIcc_local (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The symmetric window is nonempty. -/
private lemma symIcc_nonempty (N : ℕ) : (symIcc N).Nonempty :=
  ⟨0, by rw [symIcc]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-! ## The family-average comparison -/

/-- **The family average of the extended datum dominates that of `D`** (up to an `A₀`-dependent,
data-independent constant), for a datum whose top slot set has at most one slot. -/
theorem famAvg_le_extFamAvg (D : IdxDatum) (d : ℕ) (hd : 2 ≤ d) (c : ℤ)
    (hcard : Fintype.card (D.I (d - 1)) ≤ 1) (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
      ∀ (H N : ℕ) (f : ℤ → ℂ), 1 ≤ N → 1 ≤ H →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
        ((H : ℝ) + 1) ^ d ≤ (2 : ℝ) ^ d * A₀ * (N : ℝ) →
        C * D.famAvg d H c N f ≤ (extDatum D).famAvg d H c N f := by
  classical
  -- ## the constants
  set Cd : ℕ := ∑ j ∈ Finset.range d, Fintype.card ((extDatum D).S j) with hCd
  set B : ℝ := |((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ) * (((Cd : ℝ) + 1) ^ (d - 1))
      * (2 : ℝ) ^ d * A₀ with hB
  set K₀ : ℕ := Nat.ceil B + 1 with hK₀
  have hK₀pos : (0 : ℝ) < 2 * (K₀ : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K₀]
  set C : ℝ := (Real.sqrt 2)⁻¹ * (1 / 2) * ((2 * (K₀ : ℝ) + 3))⁻¹ with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact mul_pos (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))) (by norm_num))
      (inv_pos.mpr hK₀pos)
  have hCle : C ≤ 1 := by
    rw [hC]
    have h1 : (Real.sqrt 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ ((Real.one_le_sqrt (x := 2)).mpr (by norm_num))
    have h2 : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have h3 : ((2 * (K₀ : ℝ) + 3))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [hK₀pos] : (1 : ℝ) ≤ 2 * (K₀ : ℝ) + 3)
    calc (Real.sqrt 2)⁻¹ * (1 / 2) * ((2 * (K₀ : ℝ) + 3))⁻¹
        ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by norm_num)) h3 (by positivity)
            (by norm_num)
      _ = 1 := by norm_num
  refine ⟨C, hCpos, hCle, ?_⟩
  intro H N f hN hH hb1 hsu hfitd
  set N₁ : ℕ := K₀ * N + 1 with hN₁def
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; omega
  have hNN₁ : N ≤ N₁ := by
    rw [hN₁def]
    calc N ≤ K₀ * N := Nat.le_mul_of_pos_left N (by omega)
      _ ≤ K₀ * N + 1 := Nat.le_succ _
  have hN₀ : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hN₁pos : 0 < N₁ := lt_of_lt_of_le hN₀ hNN₁
  have hsu₁ : ∀ x : ℤ, x ∉ symIcc N₁ → f x = 0 :=
    supportIn_iff_forall.mp (supportIn_mono_of_le hNN₁ hsu)
  have hN₁ne : (symIcc N₁).Nonempty := symIcc_nonempty N₁
  -- ## the level-raise constant
  have hC₁ : ∀ (S : ℕ) (hS : 1 ≤ S) (Q : Fin S → Finset ℤ) {N' : ℕ} (hN' : 0 < N')
      {f' : ℤ → ℂ} (hsup' : ∀ x : ℤ, x ∉ symIcc N' → f' x = 0)
      (hbb' : ∀ x : ℤ, ‖f' x‖ ≤ 1) (hQ' : ∀ i, (Q i).Nonempty)
      (hbdd' : ∀ (i : Fin S) (z : ℤ), z ∈ Q i → |z| ≤ (N' : ℤ))
      (i₀ : Fin S) (hQ₀ : (Q i₀).Nonempty),
      (1 / 2) * boxNorm 1 (fun _ : Fin 1 => Q i₀) (symIcc N') f' ≤ boxNorm S Q (symIcc N') f' :=
    fun S hS Q N' hN' f' hsup' hbb' hQ' hbdd' i₀ hQ₀ =>
      boxNorm_le_levelRaise_half S hS Q hN' hsup' hbb' hQ' hbdd' i₀ hQ₀
  -- ## the direction fit
  have hfit : ∀ β ∈ (extDatum D).parBox d H,
      ∀ (i : Fin (Fintype.card ((extDatum D).I (d - 1)))) (z : ℤ),
        z ∈ famDirExt D d H c β i → |z| ≤ (N₁ : ℤ) := by
    intro β hβ i z hz
    have hβp : ∀ j s, -((H : ℤ)) ≤ β j s ∧ β j s ≤ (H : ℤ) := IdxDatum.mem_parBox.mp hβ
    rw [famDirExt] at hz
    obtain ⟨n, hn, hnz⟩ := Finset.mem_image.mp hz
    have hnhi : (n : ℤ) ≤ (H : ℤ) := by
      exact_mod_cast (Finset.mem_Icc.mp hn).2
    set q : ℤ := (extDatum D).dir d c (d - 1)
      ((Fintype.equivFin ((extDatum D).I (d - 1))).symm i) ((extDatum D).pad d β) with hq
    have hCd' : ∀ j' : ℕ, j' ≤ d - 1 → Fintype.card ((extDatum D).S j') ≤ Cd := by
      intro j' hj'
      rw [hCd]
      exact Finset.single_le_sum (s := Finset.range d)
        (f := fun j => Fintype.card ((extDatum D).S j)) (fun j _ => Nat.zero_le _)
        (Finset.mem_range.mpr (show j' < d from by omega))
    have ha : ∀ j' : ℕ, j' ≤ d - 1 → ∀ s : (extDatum D).S j',
        -((H : ℤ)) ≤ ((extDatum D).pad d β) j' s ∧ ((extDatum D).pad d β) j' s ≤ (H : ℤ) := by
      intro j' hj' s
      rw [IdxDatum.pad]
      split_ifs with h
      · exact hβp ⟨j', h⟩ s
      · omega
    have hdb := Work.Prop36SW.dirBound (extDatum D) d c (d - 1) H Cd
      ((Fintype.equivFin ((extDatum D).I (d - 1))).symm i)
      ((extDatum D).pad d β) hCd' ha
    have hdbq : |q| ≤ |c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
        * (((H : ℤ) + 1) ^ (d - 1)) := hdb
    have hzq : |z| ≤ |q| * (H : ℤ) := by
      rw [← hnz, abs_mul]
      have hnabs : |(n : ℤ)| = (n : ℤ) := abs_of_nonneg (by omega)
      rw [hnabs]
      exact mul_le_mul_of_nonneg_left hnhi (abs_nonneg _)
    have hcoef0 : (0 : ℤ) ≤ |c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1)) := by positivity
    have hIcc : |z| ≤ |c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
        * (((H : ℤ) + 1) ^ d) := by
      refine hzq.trans ?_
      calc |q| * (H : ℤ)
          ≤ (|c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
              * (((H : ℤ) + 1) ^ (d - 1))) * (H : ℤ) :=
            mul_le_mul_of_nonneg_right hdbq (by omega)
        _ = |c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
              * ((((H : ℤ) + 1) ^ (d - 1)) * (H : ℤ)) := by ring
        _ ≤ |c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
              * (((H : ℤ) + 1) ^ d) := by
            refine mul_le_mul_of_nonneg_left ?_ hcoef0
            have hsucc : ((H : ℤ) + 1) ^ (d - 1) * ((H : ℤ) + 1) = ((H : ℤ) + 1) ^ d := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
            rw [← hsucc]
            exact mul_le_mul_of_nonneg_left (by omega : (H : ℤ) ≤ (H : ℤ) + 1)
              (by positivity)
    -- cast to `ℝ` and use the fit hypothesis
    have hcast : ((|z| : ℤ) : ℝ) ≤ B * (N : ℝ) := by
      have h1 : ((|z| : ℤ) : ℝ) ≤ (|((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ)
          * (((Cd : ℝ) + 1) ^ (d - 1))) * ((((H : ℝ) + 1) ^ d)) := by
        have hthis := hIcc
        calc ((|z| : ℤ) : ℝ)
            ≤ ((|c| * (Nat.factorial d : ℤ) * (((Cd : ℤ) + 1) ^ (d - 1))
                * (((H : ℤ) + 1) ^ d) : ℤ) : ℝ) := by exact_mod_cast hthis
          _ = |((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ) * (((Cd : ℝ) + 1) ^ (d - 1))
                * (((H : ℝ) + 1) ^ d) := by push_cast; ring
      rw [hB]
      have h2 : (((H : ℝ) + 1) ^ d) ≤ (2 : ℝ) ^ d * A₀ * (N : ℝ) := hfitd
      have h3 : (0 : ℝ) ≤ |((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ)
          * (((Cd : ℝ) + 1) ^ (d - 1)) := by positivity
      calc ((|z| : ℤ) : ℝ)
          ≤ (|((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ) * (((Cd : ℝ) + 1) ^ (d - 1)))
              * (((H : ℝ) + 1) ^ d) := h1
        _ ≤ (|((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ) * (((Cd : ℝ) + 1) ^ (d - 1)))
              * ((2 : ℝ) ^ d * A₀ * (N : ℝ)) := mul_le_mul_of_nonneg_left h2 h3
        _ = |((c : ℤ) : ℝ)| * ((Nat.factorial d : ℕ) : ℝ) * (((Cd : ℝ) + 1) ^ (d - 1))
              * (2 : ℝ) ^ d * A₀ * (N : ℝ) := by ring
    have hBK : B ≤ (K₀ : ℝ) := by
      rw [hK₀]
      push_cast
      linarith [Nat.le_ceil B]
    have hKN : (K₀ : ℝ) * (N : ℝ) ≤ (N₁ : ℝ) := by
      rw [hN₁def]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (K₀ * N)]
    have hfin : ((|z| : ℤ) : ℝ) ≤ (N₁ : ℝ) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      calc ((|z| : ℤ) : ℝ) ≤ B * (N : ℝ) := hcast
        _ ≤ (K₀ : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right hBK hN0
        _ ≤ (N₁ : ℝ) := hKN
    exact_mod_cast hfin
  -- ## the pointwise comparison
  have hpt : ∀ β ∈ (extDatum D).parBox d H,
      C * D.famNorm d H c N (oldPart D β) f ≤ (extDatum D).famNorm d H c N β f := by
    intro β hβ
    show C * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β)) (symIcc N) f
        ≤ boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β) (symIcc N) f
    have hcomp' : (Real.sqrt 2)⁻¹ * (1 / 2)
        * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β)) (symIcc N₁) f
        ≤ boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β) (symIcc N₁) f :=
      extFamNorm_ge_at (1 / 2) (by norm_num) hC₁ D d (by omega) c H N₁ f β
        hH hN₁pos hb1 hsu₁ (hfit β hβ) hβ hcard
    set ρ : ℝ := ((symIcc N₁).card : ℝ) / ((symIcc N).card : ℝ) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact div_pos (by exact_mod_cast Finset.card_pos.mpr hN₁ne)
        (by exact_mod_cast Finset.card_pos.mpr (symIcc_nonempty N))
    have hρge : 1 ≤ ρ := by
      rw [hρdef, one_le_div (by exact_mod_cast Finset.card_pos.mpr (symIcc_nonempty N))]
      exact_mod_cast Finset.card_le_card (fun x hx => by
        rw [symIcc] at hx ⊢
        exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hx).1; omega,
          by have := (Finset.mem_Icc.mp hx).2; omega⟩)
    have hρle : ρ ≤ 2 * (K₀ : ℝ) + 3 := by
      rw [hρdef, card_symIcc_local N₁, card_symIcc_local N, hN₁def]
      push_cast
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) K₀, Nat.cast_nonneg (α := ℝ) N]
    have hTS : Fintype.card (D.I (d - 1)) ≤ Fintype.card ((extDatum D).I (d - 1)) :=
      le_trans hcard (le_trans (by norm_num) (three_le_card_extI D (d - 1)))
    have hexp1 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
        - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)) := by
      have h1 : (2 : ℝ) ^ Fintype.card (D.I (d - 1))
          ≤ 2 ^ Fintype.card ((extDatum D).I (d - 1)) :=
        pow_le_pow_right₀ (by norm_num) hTS
      have h3 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card (D.I (d - 1)) := by positivity
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le h3 h1
    have hexp2 : 1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
        - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)) ≤ 1 := by
      have h1 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)) := by positivity
      have h3 : (1 : ℝ) / (2 : ℝ) ^ Fintype.card (D.I (d - 1)) ≤ 1 := by
        rw [one_div]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      linarith [h1, h3]
    have hCineq : C * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))
        ≤ (Real.sqrt 2)⁻¹ * (1 / 2)
          * ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) := by
      have hsplit : ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))
          = ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
            * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
              - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) := by
        rw [← Real.rpow_add hρpos]
        congr 1
        ring
      have hexp3 : ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
            - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) ≤ 2 * (K₀ : ℝ) + 3 := by
        have h1 : ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
              - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) ≤ ρ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hρge hexp2
        rw [Real.rpow_one] at h1
        linarith [h1, hρle]
      rw [hC]
      calc (Real.sqrt 2)⁻¹ * (1 / 2) * (2 * (K₀ : ℝ) + 3)⁻¹
            * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))
          = (Real.sqrt 2)⁻¹ * (1 / 2)
            * ((2 * (K₀ : ℝ) + 3)⁻¹ * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))) := by ring
        _ ≤ (Real.sqrt 2)⁻¹ * (1 / 2)
            * ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hsplit, inv_mul_le_iff₀ hK₀pos]
            calc ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
                  * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))
                    - 1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
                ≤ ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
                  * (2 * (K₀ : ℝ) + 3) :=
                  mul_le_mul_of_nonneg_left hexp3 (by positivity)
              _ = (2 * (K₀ : ℝ) + 3) * ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))) :=
                  by ring
    have hboxD : boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
          (symIcc N) f
        = ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))
          * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
              (symIcc N₁) f := by
      rw [hρdef]
      exact boxNorm_symIcc_ratio (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
        (N := N) (N' := N₁) hN₁ne f
    have hboxE : boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β)
          (symIcc N) f
        = ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
          * boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β)
              (symIcc N₁) f := by
      rw [hρdef]
      exact boxNorm_symIcc_ratio (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β)
        (N := N) (N' := N₁) hN₁ne f
    rw [hboxD, hboxE]
    calc C * (ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1)))
          * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
              (symIcc N₁) f)
        = (C * ρ ^ (1 / (2 : ℝ) ^ Fintype.card (D.I (d - 1))))
            * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
                (symIcc N₁) f := by ring
      _ ≤ ((Real.sqrt 2)⁻¹ * (1 / 2)
              * ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1))))
            * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
                (symIcc N₁) f :=
          mul_le_mul_of_nonneg_right hCineq
            (by rw [boxNorm, boxNormPow]; exact Real.rpow_nonneg (norm_nonneg _) _)
      _ = ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
            * ((Real.sqrt 2)⁻¹ * (1 / 2)
              * boxNorm (Fintype.card (D.I (d - 1))) (famDirOld D d H c (oldPart D β))
                  (symIcc N₁) f) := by ring
      _ ≤ ρ ^ (1 / (2 : ℝ) ^ Fintype.card ((extDatum D).I (d - 1)))
            * boxNorm (Fintype.card ((extDatum D).I (d - 1))) (famDirExt D d H c β)
                (symIcc N₁) f :=
          mul_le_mul_of_nonneg_left hcomp' (le_of_lt (Real.rpow_pos_of_pos hρpos _))
  -- ## the averaging
  have hsum1 : ∑ β ∈ (extDatum D).parBox d H, C * D.famNorm d H c N (oldPart D β) f
      ≤ ∑ β ∈ (extDatum D).parBox d H, (extDatum D).famNorm d H c N β f :=
    Finset.sum_le_sum (fun β hβ => hpt β hβ)
  have hL : ∑ β ∈ (extDatum D).parBox d H, C * D.famNorm d H c N (oldPart D β) f
      = ((newBox d H).card : ℝ)
          * (C * ∑ a ∈ D.parBox d H, D.famNorm d H c N a f) := by
    rw [sum_extParBox, Finset.sum_product]
    simp only [oldPart_mkIdx]
    rw [Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_const, nsmul_eq_mul])]
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.mul_sum]
  have hmain : ((newBox d H).card : ℝ) * (C * ∑ a ∈ D.parBox d H, D.famNorm d H c N a f)
      ≤ ∑ β ∈ (extDatum D).parBox d H, (extDatum D).famNorm d H c N β f := by
    rw [← hL]; exact hsum1
  have hcardmul : (((extDatum D).parBox d H).card : ℝ)
      = ((D.parBox d H).card : ℝ) * ((newBox d H).card : ℝ) := by
    rw [card_extParBox]; push_cast; ring
  have hinv : (((extDatum D).parBox d H).card : ℝ)⁻¹
      = ((D.parBox d H).card : ℝ)⁻¹ * ((newBox d H).card : ℝ)⁻¹ := by
    rw [hcardmul, mul_inv]
  have hcBne : ((newBox d H).card : ℝ) ≠ 0 := by
    have hpos : 0 < (newBox d H).card := by
      rw [Finset.card_pos]
      exact ⟨fun _ => 0, mem_newBox.mpr (fun p => ⟨by omega, by omega⟩)⟩
    exact_mod_cast ne_of_gt hpos
  have hcPne : ((D.parBox d H).card : ℝ) ≠ 0 := by
    have hpos : 0 < (D.parBox d H).card := by
      rw [Finset.card_pos]
      exact ⟨fun _ _ => 0, IdxDatum.mem_parBox.mpr (fun j s => ⟨by omega, by omega⟩)⟩
    exact_mod_cast ne_of_gt hpos
  calc C * D.famAvg d H c N f
      = C * (((D.parBox d H).card : ℝ)⁻¹ * ∑ a ∈ D.parBox d H, D.famNorm d H c N a f) := rfl
    _ = (((extDatum D).parBox d H).card : ℝ)⁻¹
          * (((newBox d H).card : ℝ) * (C * ∑ a ∈ D.parBox d H, D.famNorm d H c N a f)) := by
        rw [hinv]
        field_simp
    _ ≤ (((extDatum D).parBox d H).card : ℝ)⁻¹
          * ∑ β ∈ (extDatum D).parBox d H, (extDatum D).famNorm d H c N β f :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (extDatum D).famAvg d H c N f := rfl

/-! ## The degenerate branch -/

/-- **The degenerate branch of `prop36SW_of_ladderA`.**

This is the body of `Work.Peluse.C46.Prop36SW P` at a datum `D` whose top slot set `D.S (d-1)` has
at most one element.  It reduces, through `extDatum D`, to the non-degenerate body
`Work.Peluse.prop36SW_body` applied to the extension: the rescaling `η ↦ Cη`, `A ↦ A'/C^{K'}`
(`C ∈ (0,1]` from `famAvg_le_extFamAvg`) maps the datum's hypotheses *verbatim* onto those of the
extension and leaves the window `⌊max 1 (η^K δ'^d M^d / A)⌋` unchanged. -/
theorem prop36SW_degenerate (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (h : Work.Peluse.C46.PeluseLadderA) (D : IdxDatum)
    (hcard : Fintype.card (D.I (P.natDegree - 1)) ≤ 1) :
    ∃ s : ℕ, 2 ≤ s ∧
      ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (N M : ℕ) (f : ℤ → ℂ) (η δ' : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M → (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
        (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
        0 < η → η ≤ 1 → 0 < δ' → A * δ' ≤ η ^ K →
        2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
        A * (η * δ') ^ (-(K : ℤ)) ≤ (N : ℝ) →
        η ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f →
        η ^ K ≤ A * uNormPow s
          (arithIcc (P.natDegree.factorial * P.leadingCoeff)
            (⌊max (1 : ℝ) (η ^ K * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A)⌋).toNat)
          (symIcc N) f := by
  classical
  obtain ⟨s', hs'2, hbody⟩ :=
    prop36SW_body P hd h (extDatum D) (two_le_card_extI' D (P.natDegree - 1))
  refine ⟨s', hs'2, ?_⟩
  intro A₀ hA₀
  obtain ⟨C, hCpos, hC1, hCbnd⟩ :=
    famAvg_le_extFamAvg D P.natDegree hd P.leadingCoeff hcard A₀ hA₀
  obtain ⟨A', hA'1, K', hK'1, hmain⟩ := hbody A₀ hA₀
  set A : ℝ := A' / C ^ K' with hAdef
  have hCK1 : C ^ K' ≤ 1 := pow_le_one₀ hCpos.le hC1
  have hA1 : 1 ≤ A := by
    rw [hAdef, le_div_iff₀ (pow_pos hCpos K')]
    nlinarith [hA'1, hCK1]
  refine ⟨A, hA1, K', hK'1, ?_⟩
  intro N M f η δ' h2d hN hM hNM1 hNM2 hη0 hη1 hδ' hAδ hH2 hf hsu hAη hfam
  -- ## side conditions on the datum
  have hδ1 : δ' ≤ 1 := by
    have h1 : δ' ≤ A * δ' := le_mul_of_one_le_left hδ'.le hA1
    have h2 : η ^ K' ≤ 1 := pow_le_one₀ hη0.le hη1
    linarith [h1, hAδ, h2]
  have hHn1 : 1 ≤ (⌊δ' * (M : ℝ)⌋).toNat := by omega
  have hfl0 : (0 : ℤ) ≤ ⌊δ' * (M : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have hHn_le : (((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) ≤ δ' * (M : ℝ) := by
    have h1 : (((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) = ((⌊δ' * (M : ℝ)⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hfl0]
    rw [h1]
    exact_mod_cast Int.floor_le (δ' * (M : ℝ))
  have hδM1 : (1 : ℝ) ≤ δ' * (M : ℝ) :=
    le_trans (by exact_mod_cast hHn1) hHn_le
  have hfitd : ((((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) + 1) ^ P.natDegree
      ≤ (2 : ℝ) ^ P.natDegree * A₀ * (N : ℝ) := by
    have h1 : (((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) + 1 ≤ 2 * (δ' * (M : ℝ)) := by
      linarith
    have h2 : ((((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) + 1) ^ P.natDegree
        ≤ (2 * (δ' * (M : ℝ))) ^ P.natDegree :=
      pow_le_pow_left₀ (by positivity) h1 _
    have h3 : (2 * (δ' * (M : ℝ))) ^ P.natDegree
        = 2 ^ P.natDegree * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := by ring
    have h4 : δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree ≤ (M : ℝ) ^ P.natDegree := by
      have hδd : δ' ^ P.natDegree ≤ 1 := pow_le_one₀ hδ'.le hδ1
      nlinarith [hδd, pow_nonneg (Nat.cast_nonneg (α := ℝ) M) P.natDegree]
    have h5 : (2 : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree
        ≤ (2 : ℝ) ^ P.natDegree * A₀ * (N : ℝ) := by
      have h6 : (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) := hNM2
      have h7 : (0 : ℝ) < (2 : ℝ) ^ P.natDegree := by positivity
      nlinarith [h6, h7]
    calc ((((⌊δ' * (M : ℝ)⌋).toNat : ℕ) : ℝ) + 1) ^ P.natDegree
        ≤ (2 * (δ' * (M : ℝ))) ^ P.natDegree := h2
      _ = 2 ^ P.natDegree * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := h3
      _ ≤ 2 ^ P.natDegree * (M : ℝ) ^ P.natDegree :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ 2 ^ P.natDegree * A₀ * (N : ℝ) := h5
  have hfamExt : C * η ≤ (extDatum D).famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat
      P.leadingCoeff N f := by
    calc C * η ≤ C * D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f :=
          mul_le_mul_of_nonneg_left hfam hCpos.le
      _ ≤ (extDatum D).famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f :=
          hCbnd _ N f hN hHn1 hf hsu hfitd
  -- ## the rescaled hypotheses for the extension
  have hcηpos : 0 < C * η := mul_pos hCpos hη0
  have hcη1 : C * η ≤ 1 := by nlinarith [hCpos, hC1, hη0, hη1]
  have hAδ' : A' * δ' ≤ (C * η) ^ K' := by
    have hck : (0 : ℝ) < C ^ K' := pow_pos hCpos K'
    have h1 : A' * δ' = (A' / C ^ K') * δ' * C ^ K' := by field_simp
    rw [h1]
    calc (A' / C ^ K') * δ' * C ^ K' ≤ η ^ K' * C ^ K' :=
          mul_le_mul_of_nonneg_right hAδ hck.le
      _ = (C * η) ^ K' := by rw [mul_pow]; ring
  have hrew : ((C * η) * δ') ^ (-(K' : ℤ)) = (C ^ K')⁻¹ * (η * δ') ^ (-(K' : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow, mul_pow, mul_inv, mul_inv]
    ring
  have hAη' : A' * ((C * η) * δ') ^ (-(K' : ℤ)) = A * (η * δ') ^ (-(K' : ℤ)) := by
    rw [hrew, hAdef, div_eq_mul_inv]
    ring
  have hAη'' : A' * ((C * η) * δ') ^ (-(K' : ℤ)) ≤ (N : ℝ) := by
    rw [hAη']
    exact hAη
  -- ## the conclusion of the chain for the extension
  have hfin : (C * η) ^ K' ≤ A' * uNormPow s'
      (arithIcc (P.natDegree.factorial * P.leadingCoeff)
        (⌊max (1 : ℝ) ((C * η) ^ K' * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A')⌋).toNat)
      (symIcc N) f :=
    hmain N M f (C * η) δ' h2d hN hM hNM1 hNM2 hcηpos hcη1 hδ' hAδ' hH2 hf hsu hAη'' hfamExt
  -- ## the window is unchanged
  have hck : (0 : ℝ) < C ^ K' := pow_pos hCpos K'
  have harg : max (1 : ℝ) ((C * η) ^ K' * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A')
      = max (1 : ℝ) (η ^ K' * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A) := by
    congr 1
    rw [hAdef, mul_pow, div_eq_mul_inv, div_eq_mul_inv]
    field_simp
  rw [harg] at hfin
  -- ## rescaled conclusion
  calc η ^ K' = (C * η) ^ K' / C ^ K' := by rw [mul_pow]; field_simp
    _ ≤ (A' * uNormPow s'
          (arithIcc (P.natDegree.factorial * P.leadingCoeff)
            (⌊max (1 : ℝ) (η ^ K' * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A)⌋).toNat)
          (symIcc N) f) / C ^ K' := div_le_div_of_nonneg_right hfin hck.le
    _ = A * uNormPow s'
          (arithIcc (P.natDegree.factorial * P.leadingCoeff)
            (⌊max (1 : ℝ) (η ^ K' * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A)⌋).toNat)
          (symIcc N) f := by
        rw [hAdef, div_eq_mul_inv]
        ring

end

end Work.Peluse
