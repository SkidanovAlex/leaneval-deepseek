import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.rayHilb_finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary facts about the multigraded pieces `pieceZ`

Small technical facts used by `Work.BW.rayDeg_additive` and by the lemmas delegated around it:
the pieces of negative multidegree vanish, the pieces are finite-dimensional, and `hilbIdeal` is
antitone in the ideal.
-/

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-- Every coordinate of the weight of a monomial with respect to `wZ` is nonnegative. -/
theorem weight_wZ_apply_nonneg (N : ℕ) (d : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    0 ≤ Finsupp.weight (wZ N) d i := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add a b f haf hb ih =>
      rw [map_add, Finsupp.weight_single, Finsupp.add_apply]
      refine add_nonneg ?_ ih
      rw [Finsupp.smul_apply, wZ, Finsupp.single_apply]
      refine nsmul_nonneg ?_ b
      split_ifs <;> norm_num

private theorem castF_add_aux {N : ℕ} (x y : Fin (N + 1) →₀ ℕ) :
    castF (x + y) = castF x + castF y := by
  ext i; simp [castF_apply]

private theorem castF_nsmul_aux {N : ℕ} (k : ℕ) (x : Fin (N + 1) →₀ ℕ) :
    castF (k • x) = k • castF x := by
  ext i; simp [castF_apply]

private theorem castF_single_aux {N : ℕ} (i : Fin (N + 1)) (k : ℕ) :
    castF (Finsupp.single i k) = Finsupp.single i (k : ℤ) := by
  ext j
  by_cases h : i = j
  · subst h; simp [castF_apply]
  · rw [castF_apply, Finsupp.single_eq_of_ne (Ne.symm h)]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]

private theorem castF_zero_aux {N : ℕ} : castF (0 : Fin (N + 1) →₀ ℕ) = 0 := by
  ext i; simp [castF_apply]

private theorem weight_mdeg_eq_aux (N : ℕ) (s : Fin (N + 1) × Fin 2 →₀ ℕ) :
    castF (Finsupp.weight (mdeg N) s) = Finsupp.weight (wZ N) s := by
  induction s using Finsupp.induction with
  | zero => simp [castF_zero_aux]
  | single_add a b f haf hb ih =>
      have h1 : Finsupp.weight (mdeg N) (Finsupp.single a b + f)
          = b • mdeg N a + Finsupp.weight (mdeg N) f := by
        rw [map_add, Finsupp.weight_single]
      have h2 : Finsupp.weight (wZ N) (Finsupp.single a b + f)
          = b • wZ N a + Finsupp.weight (wZ N) f := by
        rw [map_add, Finsupp.weight_single]
      rw [h1, h2, castF_add_aux, castF_nsmul_aux, ih]
      congr 1
      simp [mdeg, wZ, castF_single_aux]

private theorem homPiece_eq_pieceZ_aux (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    homPiece N d = pieceZ N (castF d) := by
  ext p
  simp only [homPiece, pieceZ, MvPolynomial.mem_weightedHomogeneousSubmodule]
  constructor
  · intro h s hs
    rw [← weight_mdeg_eq_aux, h hs]
  · intro h s hs
    have h' := h hs
    rw [← weight_mdeg_eq_aux] at h'
    have h'' : ∀ i, ((Finsupp.weight (mdeg N) s) i : ℤ) = (d i : ℤ) := by
      intro i
      have := congrArg (fun f : Fin (N + 1) →₀ ℤ => f i) h'
      simpa [castF_apply] using this
    ext i
    exact Int.ofNat.inj (h'' i)

/-- The piece of negative multidegree vanishes. -/
private theorem pieceZ_eq_bot_of_neg (N : ℕ) (u : Fin (N + 1) →₀ ℤ) (h : ∃ i, u i < 0) :
    pieceZ N u = ⊥ := by
  obtain ⟨i, hi⟩ := h
  rw [Submodule.eq_bot_iff]
  intro q hq
  rw [mem_pieceZ] at hq
  ext d
  by_contra hd
  have h1 : 0 ≤ (Finsupp.weight (wZ N) d) i := weight_wZ_apply_nonneg N d i
  rw [hq hd] at h1
  omega

private noncomputable def toNatF_aux {N : ℕ} (u : Fin (N + 1) →₀ ℤ) : Fin (N + 1) →₀ ℕ :=
  u.mapRange Int.toNat (by simp)

private theorem castF_toNatF_aux {N : ℕ} (u : Fin (N + 1) →₀ ℤ) (h : ∀ i, 0 ≤ u i) :
    castF (toNatF_aux u) = u := by
  ext i
  simp only [castF_apply, toNatF_aux, Finsupp.mapRange_apply]
  exact Int.toNat_of_nonneg (h i)

/-- Every multigraded piece of the coordinate ring is finite-dimensional over `ℂ`. -/
theorem moduleFinite_pieceZ (N : ℕ) (u : Fin (N + 1) →₀ ℤ) :
    Module.Finite ℂ ↥(pieceZ N u) := by
  by_cases h : ∃ i, u i < 0
  · rw [pieceZ_eq_bot_of_neg N u h]
    infer_instance
  · push_neg at h
    rw [← castF_toNatF_aux u h, ← homPiece_eq_pieceZ_aux, homPiece]
    exact rayHilb_finite N (toNatF_aux u)

theorem finrank_quotient_le_of_le {M : Type*} [AddCommGroup M] [Module ℂ M]
    {p q : Submodule ℂ M} (h : p ≤ q) [Module.Finite ℂ M] :
    Module.finrank ℂ (M ⧸ q) ≤ Module.finrank ℂ (M ⧸ p) := by
  haveI : Module.Finite ℂ ↥q :=
    Module.Finite.of_injective (Submodule.subtype q) (Submodule.subtype_injective q)
  have h1 : Module.finrank ℂ (M ⧸ p) + Module.finrank ℂ p = Module.finrank ℂ M :=
    Submodule.finrank_quotient_add_finrank p
  have h2 : Module.finrank ℂ (M ⧸ q) + Module.finrank ℂ q = Module.finrank ℂ M :=
    Submodule.finrank_quotient_add_finrank q
  have h3 : Module.finrank ℂ p ≤ Module.finrank ℂ q := Submodule.finrank_mono h
  omega

/-- `hilbIdeal` is antitone in the ideal. -/
theorem hilbIdeal_anti (N : ℕ) {J₁ J₂ : Ideal (MR N)} (h : J₁ ≤ J₂) (u : Fin (N + 1) →₀ ℤ) :
    hilbIdeal N J₂ u ≤ hilbIdeal N J₁ u := by
  haveI := moduleFinite_pieceZ N u
  refine finrank_quotient_le_of_le ?_
  intro x hx
  exact h hx

end Work.BW
