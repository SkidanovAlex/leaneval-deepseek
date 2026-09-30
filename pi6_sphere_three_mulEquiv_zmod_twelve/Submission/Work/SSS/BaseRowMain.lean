import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.FgQuotBasic
import Submission.Work.SSS.Lem.finite_homology_iff
import Submission.Work.SSS.Lem.fgQuot_baseZ_of_baseJ
import Submission.Work.SSS.Lem.fgQuot_Psi
import Submission.Work.SSS.Lem.fgQuot_Psi_zero
import Submission.Work.SSS.Lem.fgQuot_baseZ_terminal

/-!
# The bottom row of the spectral sequence of a saturated filtration

This file assembles the bottom-row edge statement `Work.SSS.baseRow`: the `E²` term `E²_{m+1,0}` of
the spectral sequence of a saturated filtration `ξ` of a chain complex `C` of `ℤ`-modules is
finitely generated as soon as `H_{m+1}(C)` is and the `E²` terms of total degree `m` are.

The proof uses the chain of submodules `baseZ ξ m 2 ⊇ baseZ ξ m 3 ⊇ … ⊇ baseZ ξ m (m+2)` of
`E¹_{m+1,0}`, whose successive quotients are the strata `Ψ_s/Ψ_{s-1}` of the image filtration of
`H_m(F_m)` (hence subquotients of the `E²` page in total degree `m`), together with the
identifications `baseZ ξ m (m+2) = ker (k : E¹_{m+1,0} → H_m(F_m))` and
`baseB ξ m = im (d¹ : E¹_{m+2,0} → E¹_{m+1,0})`.
-/

set_option autoImplicit false

set_option maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- `Psi` increases by one step, as long as the next index is still `≤ m`. -/
theorem Psi_mono_aux (ξ : Filtration C) (m s : ℕ) (hs : s + 1 ≤ m) :
    Psi ξ m s ≤ Psi ξ m (s + 1) := by
  have h1 : s ≤ m := by omega
  rw [Psi, dif_pos h1, Psi, dif_pos hs]
  rw [show ξ.F.map (homOfLE h1) =
      ξ.F.map (homOfLE (show s ≤ s + 1 by omega)) ≫ ξ.F.map (homOfLE hs) from by
    rw [← Functor.map_comp, homOfLE_comp]]
  rw [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  exact LinearMap.range_comp_le_range _ _

/-- `Psi` is monotone on the indices `≤ m`. -/
theorem Psi_mono_of_le (ξ : Filtration C) (m : ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    Psi ξ m a ≤ Psi ξ m b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  suffices h : ∀ k : ℕ, a + k ≤ m → Psi ξ m a ≤ Psi ξ m (a + k) from h k hb
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      refine le_trans (ih (by omega)) ?_
      rw [show a + (k + 1) = (a + k) + 1 by omega]
      exact Psi_mono_aux ξ m (a + k) (by omega)

/-- `baseJ ξ m` is antitone on the indices `≥ 1`. -/
theorem baseJ_antitone (ξ : Filtration C) (m : ℕ) {r r' : ℕ} (hr : 1 ≤ r) (hrr' : r ≤ r') :
    baseJ ξ m r' ≤ baseJ ξ m r := by
  have h2 : ∀ r : ℕ, 1 ≤ r → r ≤ m + 1 → baseJ ξ m r = Psi ξ m (m + 1 - r) := by
    intro r _ hr'
    rw [baseJ, dif_pos hr']
  by_cases h : r' ≤ m + 1
  · have h1 : baseJ ξ m r' = Psi ξ m (m + 1 - r') := h2 r' (le_trans hr hrr') h
    have h3 : baseJ ξ m r = Psi ξ m (m + 1 - r) := h2 r hr (by omega)
    rw [h1, h3]
    exact Psi_mono_of_le ξ m (show m + 1 - r' ≤ m + 1 - r by omega)
      (show m + 1 - r ≤ m by omega)
  · rw [baseJ, dif_neg h]
    exact bot_le

/-- `baseZ ξ m` is antitone on the indices `≥ 1`. -/
theorem baseZ_antitone (ξ : Filtration C) (m : ℕ) {r r' : ℕ} (hr : 1 ≤ r) (hrr' : r ≤ r') :
    baseZ ξ m r' ≤ baseZ ξ m r :=
  Submodule.comap_mono (baseJ_antitone ξ m hr hrr')

/-- `baseZ ξ m r = ker k` for `r ≥ m + 2`. -/
theorem baseZ_eq_ker (ξ : Filtration C) (m r : ℕ) (hr : m + 2 ≤ r) :
    baseZ ξ m r = LinearMap.ker (kF ξ m 0).hom := by
  rw [baseZ, show baseJ ξ m r = ⊥ by rw [baseJ, dif_neg (by omega)]]
  rfl

/-- The kernel of `jF ξ m 0` is `baseJ ξ m 2`. -/
theorem ker_jF_zero_eq_baseJ_two (ξ : Filtration C) (m : ℕ) :
    LinearMap.ker (jF ξ m 0).hom = baseJ ξ m 2 := by
  rcases m with _ | m'
  · have h : baseJ ξ 0 2 = ⊥ := by rw [baseJ, dif_neg (by omega)]
    rw [h, jF]
    exact LinearMap.ker_id
  · have hle : m' ≤ m' + 1 := by omega
    rw [baseJ, dif_pos (show 2 ≤ m' + 1 + 1 by omega),
      show m' + 1 + 1 - 2 = m' from rfl, Psi, dif_pos hle]
    have hmap : ξ.F.map (homOfLE hle) = incF ξ.F m' := by
      rw [incF]
    rw [ker_jF_eq_range_incF ξ m' 0, ← hmap]

/-- `baseZ ξ m 2` is the kernel of the first differential `d¹ : E¹_{m+1,0} → E¹_{m,0}`. -/
theorem ker_d1_eq_baseZ_two (ξ : Filtration C) (m : ℕ) :
    LinearMap.ker (d1 ξ m 0).hom = baseZ ξ m 2 := by
  rw [d1, ModuleCat.hom_comp, LinearMap.ker_comp, ker_jF_zero_eq_baseJ_two ξ m]
  rfl

/-- `baseB ξ m` is contained in `ker (k : E¹_{m+1,0} → H_m(F_m))`. -/
theorem baseB_le_ker_kF (ξ : Filtration C) (m : ℕ) :
    baseB ξ m ≤ LinearMap.ker (kF ξ m 0).hom := by
  rw [baseB, d1, ModuleCat.hom_comp]
  refine le_trans (LinearMap.range_comp_le_range _ _) ?_
  rw [range_jF_eq_ker_kF]
  exact le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem finite_E2_succ_iff (ξ : Filtration C) (m : ℕ) :
    Module.Finite ℤ (E2 ξ (m + 1) 0) ↔
      FgQuot (LinearMap.range (d1 ξ (m + 1) 0).hom) (LinearMap.ker (d1 ξ m 0).hom) := by
  rw [show E2 ξ (m + 1) 0 = (E1Complex ξ 0).homology (m + 1) from rfl,
    Work.SSS.Lem.finite_homology_iff (E1Complex ξ 0) (m + 1),
    show (E1Complex ξ 0).d (m + 2) (m + 1) = d1 ξ (m + 1) 0 from
      ChainComplex.of_d (fun s => E1 ξ s 0) (fun s => d1 ξ s 0) (m + 1),
    show (E1Complex ξ 0).d (m + 1) (m + 1 - 1) = d1 ξ m 0 from
      ChainComplex.of_d (fun s => E1 ξ s 0) (fun s => d1 ξ s 0) (m + 1 - 1)]

/-- **The bottom row statement for `n = m + 1`**, in the `FgQuot` formulation. -/
theorem fgQuot_baseB_baseZ_two (ξ : Filtration C) (m : ℕ)
    (hH : Module.Finite ℤ (C.homology (m + 1)))
    (hE : ∀ r : ℕ, 2 ≤ r → r ≤ m + 1 → Module.Finite ℤ (E2 ξ (m + 1 - r) (r - 1))) :
    FgQuot (baseB ξ m) (baseZ ξ m 2) := by
  classical
  -- From `Module.Finite ℤ (E²_{s,t})` to the explicit description `E2quot ξ s t`.
  have hquot : ∀ s t : ℕ, Module.Finite ℤ (E2 ξ s t) → E2quot ξ s t := fun s t h =>
    (Work.SSS.Lem.finite_homology_iff (E1Complex ξ t) s).mp h
  -- The successive quotients `baseZ ξ m r / baseZ ξ m (r+1)`.
  have hstep : ∀ r : ℕ, 2 ≤ r → r ≤ m + 1 → FgQuot (baseZ ξ m (r + 1)) (baseZ ξ m r) := by
    intro r hr hr'
    refine Work.SSS.Lem.fgQuot_baseZ_of_baseJ ξ m r (by omega) ?_
    by_cases hrm : r = m + 1
    · subst hrm
      rw [show baseJ ξ m (m + 1 + 1) = ⊥ by rw [baseJ, dif_neg (by omega)],
        show baseJ ξ m (m + 1) = Psi ξ m 0 by
          rw [baseJ, dif_pos (by omega), show m + 1 - (m + 1) = 0 by omega]]
      refine Work.SSS.Lem.fgQuot_Psi_zero ξ m (by omega) ?_
      have h0 : Module.Finite ℤ (E2 ξ 0 m) := by
        have h1 := hE (m + 1) (by omega) (le_refl _)
        rwa [show m + 1 - (m + 1) = 0 by omega, show m + 1 - 1 = m by omega] at h1
      exact hquot 0 m h0
    · have hrm' : r ≤ m := by omega
      rw [show baseJ ξ m (r + 1) = Psi ξ m ((m + 1 - r) - 1) by
            rw [baseJ, dif_pos (by omega)]
            congr 1,
        show baseJ ξ m r = Psi ξ m (m + 1 - r) by rw [baseJ, dif_pos (by omega)]]
      refine Work.SSS.Lem.fgQuot_Psi ξ m (m + 1 - r) (by omega) (by omega) ?_
      have hr0 : Module.Finite ℤ (E2 ξ (m + 1 - r) (r - 1)) := hE r hr hr'
      have hq : E2quot ξ (m + 1 - r) (r - 1) := hquot _ _ hr0
      rwa [show m - (m + 1 - r) = r - 1 by omega]
  -- The chain of submodules from `baseZ ξ m (m+2)` down to `baseZ ξ m 2`.
  have hchain : ∀ k : ℕ, k ≤ m → FgQuot (baseB ξ m) (baseZ ξ m (m + 2 - k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using Work.SSS.Lem.fgQuot_baseZ_terminal ξ m hH
    | succ k ih =>
        intro hk
        have h1 : FgQuot (baseB ξ m) (baseZ ξ m (m + 2 - k)) := ih (by omega)
        have h2 : FgQuot (baseZ ξ m (m + 2 - k)) (baseZ ξ m (m + 1 - k)) := by
          have h3 := hstep (m + 1 - k) (by omega) (by omega)
          simpa [show m + 1 - k + 1 = m + 2 - k by omega] using h3
        simpa [show m + 2 - (k + 1) = m + 1 - k by omega] using
          h1.of_le_of_le (baseZ_antitone ξ m (by omega) (by omega)) h2
  have hfin := hchain m le_rfl
  simpa [show m + 2 - m = 2 by omega] using hfin

end

end Work.SSS
