import Mathlib
import Submission.Work.Mostow.cardKernelTorus
import Submission.Work.Mostow.resStdDiscreteStrata
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.nrmStdMulAndRotNConj
import Submission.Work.Mostow.orthFrobenius
import Submission.Work.Mostow.centralizer_mem_SetStabStd

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
/-! **The kernel of `resStd` on the centraliser of a block element is `≤ J (1 + (rotN R) ^ (-(m/2)))`.**

Setting: `Λ ≤ PO (k+m) 1` discrete, `b = blk k m 1 R ∈ Λ` with `Fix b = stdTG k m` (equivalently
`R` has no fixed vector: `blk_smul_fermi` + `fermi_inv` identify the fixed set of `blk k m 1 R` with
`stdTG k m`), `C := Subgroup.centralizer {b} ⊓ Λ`, and the minimality hypothesis
`rotN R ≤ rotN (nrmStd k m c)` for every `c ∈ C`, `c ≠ 1`.  Then

`Nat.card {c // c ∈ Λ ∧ c ∈ centralizer {b} ∧ resStd k m c = 1} ≤ J * (1 + (rotN R) ^ (-(m/2)))`.

Route.
* `Work.Mostow.resStdDiscreteStrata` provides the multiplicativity of `resStd` on `SetStabStd k m`
  (`resStd_mul`, `resStd_one`, `resStd_inv`, `stab_form`, `mul_mem_stab`, `one_mem_stab`,
  `inv_mem_stab` are all in that file and are non-private), and `Work.Mostow.stab_eq_blk` gives
  `g = blk k m (resStd k m g) (nrmStd k m g)` for `g ∈ SetStabStd k m`.
* Copy the pattern of `resStd_mul` to get `nrmStd k m (g * h) = nrmStd k m g * nrmStd k m h` for
  `g, h ∈ SetStabStd k m` (compare `blk` decompositions via
  `(Work.Mostow.blk_hom k m hAk hIk hA hI).1` and the injectivity of clause `.2.2`).
* Every element of `C` preserves `Fix b = stdTG k m` (it commutes with `b`), hence lies in
  `SetStabStd k m`; and if `resStd k m c = 1` then `c = blk k m 1 (nrmStd k m c)`.  So the set `K`
  of the statement is the kernel of the homomorphism `c ↦ resStd k m c` on the subgroup
  `C ⊓ SetStabStd k m` (package `SetStabStd k m` as a `Subgroup` using the three lemmas above).
* The map `φ : c ↦ nrmStd k m c` is multiplicative on that subgroup and injective on `K`
  (`c = blk k m 1 (nrmStd k m c)` plus `blk` injectivity), so `Nat.card K = Nat.card (K.map φ)`,
  and the minimality hypothesis says that every non-identity element of the subgroup
  `K.map φ ≤ (E m ≃ₗᵢ[ℝ] E m)` has `rotN ≥ rotN R > 0` (positivity of `rotN R` follows from
  `R ≠ 1`, which follows from the no-fixed-vector hypothesis, e.g. via
  `orth_eq_one_of_rotN_eq_zero`).
* Apply `Work.Mostow.cardKernelTorus m` with `v := rotN R`.  (If `K` is infinite then
  `Nat.card K = 0` and the claim is trivial, so no finiteness input is needed.) -/
theorem cardKernelStrata (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k) (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) : ∃ J : ℝ, 0 < J ∧ ∀ (Λ : Subgroup (PO (k + m) 1)) (R : E m ≃ₗᵢ[ℝ] E m), IsDiscrete (SetLike.coe Λ) → blk k m 1 R ∈ Λ → (∀ w, R w = w → w = 0) → (∀ c ∈ (Subgroup.centralizer {blk k m 1 R} ⊓ Λ : Subgroup (PO (k + m) 1)), c ≠ 1 → rotN R ≤ rotN (nrmStd k m c)) → (Nat.card {c : PO (k + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk k m 1 R} ∧ resStd k m c = 1} : ℝ) ≤ J * (1 + (rotN R) ^ (-(m / 2 : ℕ) : ℤ)) := by
  obtain ⟨J₀, hJ₀pos, hJ₀⟩ := cardKernelTorus m
  refine ⟨max (2 * J₀) 1, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro Λ R hdisc hb hR hmin
  -- the centraliser of `b = blk k m 1 R` preserves the standard stratum
  have hcent : ∀ c : PO (k + m) 1,
      c ∈ Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1)) → c ∈ SetStabStd k m :=
    fun c hc => centralizer_mem_SetStabStd k m hAk hIk hA hI R hR c hc
  -- the kernel set
  let S : Set (PO (k + m) 1) :=
    {c | c ∈ Λ ∧ c ∈ Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1)) ∧
      resStd k m c = 1}
  -- every element of the kernel set is a pure block element
  have hSform : ∀ c : PO (k + m) 1, c ∈ Λ →
      c ∈ Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1)) → resStd k m c = 1 →
      c = blk k m 1 (nrmStd k m c) := by
    intro c hcΛ hcC hcS
    have h := RdsAux.stab_form k m hAk hIk hA hI (hcent c hcC)
    rw [hcS] at h
    exact h
  have hScmul : ∀ c d : PO (k + m) 1, c ∈ S → d ∈ S → c * d ∈ S := by
    rintro c d ⟨hcΛ, hcC, hcS⟩ ⟨hdΛ, hdC, hdS⟩
    exact ⟨Λ.mul_mem hcΛ hdΛ,
      (Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1))).mul_mem hcC hdC, by
        rw [RdsAux.resStd_mul k m hAk hIk hA hI (hcent c hcC) (hcent d hdC), hcS, hdS, mul_one]⟩
  have hSone : (1 : PO (k + m) 1) ∈ S :=
    ⟨one_mem Λ, Subgroup.one_mem _, RdsAux.resStd_one k m hAk hIk hA hI⟩
  have hSinv : ∀ c : PO (k + m) 1, c ∈ S → c⁻¹ ∈ S := by
    rintro c ⟨hcΛ, hcC, hcS⟩
    exact ⟨Λ.inv_mem hcΛ,
      (Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1))).inv_mem hcC, by
        rw [RdsAux.resStd_inv k m hAk hIk hA hI (hcent c hcC), hcS, inv_one]⟩
  -- the image of the kernel set under `nrmStd` is a subgroup of `O(m)`
  let T : Set (E m ≃ₗᵢ[ℝ] E m) := nrmStd k m '' S
  have hTone : (1 : E m ≃ₗᵢ[ℝ] E m) ∈ T :=
    ⟨1, hSone, rhd_nrmStd_one k m hAk hIk hA hI⟩
  have hTmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := by
    rintro a ⟨c, hc, rfl⟩ b ⟨d, hd, rfl⟩
    exact ⟨c * d, hScmul c d hc hd,
      rhd_nrmStd_mul k m hAk hIk hA hI (hcent c hc.2.1) (hcent d hd.2.1)⟩
  have hTinv : ∀ a ∈ T, a⁻¹ ∈ T := by
    rintro a ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, hSinv c hc, rhd_nrmStd_inv k m hAk hIk hA hI (hcent c hc.2.1)⟩
  let A : Subgroup (E m ≃ₗᵢ[ℝ] E m) :=
    { carrier := T
      mul_mem' := fun ha hb => hTmul _ ha _ hb
      one_mem' := hTone
      inv_mem' := fun ha => hTinv _ ha }
  have hmemA : ∀ c : PO (k + m) 1, c ∈ S → nrmStd k m c ∈ A := fun c hc => ⟨c, hc, rfl⟩
  -- the kernel set is in bijection with `A`
  have hinj : Function.Injective
      (fun c : ↥S => (⟨nrmStd k m (c : PO (k + m) 1), hmemA _ c.2⟩ : ↥A)) := by
    intro c d hcd
    have h1 : nrmStd k m (c : PO (k + m) 1) = nrmStd k m (d : PO (k + m) 1) :=
      congrArg Subtype.val hcd
    refine Subtype.ext ?_
    rw [hSform (c : PO (k + m) 1) c.2.1 c.2.2.1 c.2.2.2,
      hSform (d : PO (k + m) 1) d.2.1 d.2.2.1 d.2.2.2, h1]
  have hsurj : Function.Surjective
      (fun c : ↥S => (⟨nrmStd k m (c : PO (k + m) 1), hmemA _ c.2⟩ : ↥A)) := by
    rintro ⟨a, ha⟩
    obtain ⟨c, hc, hca⟩ := show ∃ x, x ∈ S ∧ nrmStd k m x = a from ha
    exact ⟨⟨c, hc⟩, Subtype.ext hca⟩
  have hcard_eq : Nat.card ↥S = Nat.card ↥A :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  -- the minimality hypothesis `v`-separates `A` from the identity
  have hsep : ∀ a ∈ A, a ≠ 1 → rotN R ≤ rotN a := by
    intro a ha ha1
    obtain ⟨c, hc, hca⟩ := show ∃ x, x ∈ S ∧ nrmStd k m x = a from ha
    have hcne : (c : PO (k + m) 1) ≠ 1 := by
      intro hc1
      exact ha1 (by rw [← hca, hc1, rhd_nrmStd_one k m hAk hIk hA hI])
    have h := hmin c (Subgroup.mem_inf.mpr ⟨hc.2.1, hc.1⟩) hcne
    simpa [hca] using h
  have hvnn : (0 : ℝ) ≤ rotN R := by rw [orth_rotN_eq]; exact norm_nonneg _
  have hJmax : (0 : ℝ) < max (2 * J₀) 1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  change (Nat.card ↥S : ℝ) ≤ max (2 * J₀) 1 * (1 + (rotN R) ^ (-(m / 2 : ℕ) : ℤ))
  by_cases hfin : Finite ↥S
  · haveI : Finite ↥S := hfin
    haveI : Finite ↥A := Finite.of_surjective _ hsurj
    rw [hcard_eq]
    by_cases h0 : rotN R = 0
    · -- degenerate case: `R = 1` and `E m` is a subsingleton, so `A` is trivial
      have hR1 : R = 1 := orth_eq_one_of_rotN_eq_zero R h0
      have hzero : ∀ w : E m, w = 0 := fun w => hR w (by simp [hR1])
      haveI : Subsingleton (E m ≃ₗᵢ[ℝ] E m) :=
        ⟨fun f g => LinearIsometryEquiv.ext (fun x => (hzero (f x)).trans (hzero (g x)).symm)⟩
      have h1sep : ∀ a ∈ A, a ≠ 1 → (1 : ℝ) ≤ rotN a :=
        fun a _ ha => absurd (Subsingleton.elim a 1) ha
      have hle1 := hJ₀ A 1 (by norm_num) h1sep
      rw [one_zpow] at hle1
      rw [h0]
      have hp : (0 : ℝ) ≤ (0 : ℝ) ^ (-(m / 2 : ℕ) : ℤ) := zpow_nonneg le_rfl _
      calc (Nat.card ↥A : ℝ) ≤ J₀ * (1 + 1) := hle1
        _ = 2 * J₀ := by ring
        _ ≤ max (2 * J₀) 1 := le_max_left _ _
        _ = max (2 * J₀) 1 * 1 := (mul_one _).symm
        _ ≤ max (2 * J₀) 1 * (1 + (0 : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hJmax)
    · have hv : 0 < rotN R := lt_of_le_of_ne hvnn (Ne.symm h0)
      have hle := hJ₀ A (rotN R) hv hsep
      refine le_trans hle ?_
      refine mul_le_mul_of_nonneg_right (le_max_of_le_left ?_) ?_
      · linarith
      · have hp : (0 : ℝ) ≤ (rotN R) ^ (-(m / 2 : ℕ) : ℤ) := zpow_nonneg hvnn _
        linarith
  · -- infinite kernel: `Nat.card = 0` and the bound is trivial
    have hS0 : Nat.card ↥S = 0 :=
      Nat.card_eq_zero.mpr (Or.inr ((not_finite_iff_infinite).mp hfin))
    have hp : (0 : ℝ) ≤ (rotN R) ^ (-(m / 2 : ℕ) : ℤ) := zpow_nonneg hvnn _
    rw [hS0, Nat.cast_zero]
    exact mul_nonneg (le_of_lt hJmax) (by linarith)

end Work.Mostow
