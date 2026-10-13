/-
  WilG4c / `FibreLimitPiChar` — the membership characterisations of the pieces of the
  general-`n` fibre-limit construction, and the two semantic set equalities
  `BcP = CoreP`, `(CoreP)ᶜ = LimeqP`.
-/
import Mathlib
import Submission.Work.WilG4c.FibreLimitPiBasic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0

variable {p n : ℕ}

/-! ## 1  The big set -/

theorem BigSetP_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (z : Fin (NB p n) → ℝ) :
    z ∈ BigSetP p n A ↔
      (fun j : Fin (Wp p n) => z (iotaP p n j)) ∈ A ∧ 0 < z (eIdxP p n) ∧
      z (rIdxP p n) ≠ 0 ∧
      (∀ j : Fin (n+1), (z (yIdxP p n j) - z (y0IdxP p n j)) ^ 2 ≤ (z (rIdxP p n)) ^ 2) ∧
      (∃ j : Fin (n+1), z (yIdxP p n j) ≠ z (y0IdxP p n j)) ∧
      (z (eIdxP p n)) ^ 2 < (z (vIdxP p n) - z (v0IdxP p n)) ^ 2 := by
  simp only [BigSetP, pPullP, pPosEP, pRneP, pSqAllP, pSqP, pYneP, pYneqP, pEpsP,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq, and_assoc]

/-! ## 2  `G1` and the pieces obtained by projections and complements -/

theorem G1P_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (ξ : Fin (W2 p n) → ℝ) :
    ξ ∈ G1P p n A ↔ ∃ (x : Fin (n+1) → ℝ) (v : ℝ), ZgenP p n ξ x v ∈ BigSetP p n A := by
  rw [G1P, projLastIter_eq (W2 p n) (n+2) (BigSetP p n A)]
  constructor
  · rintro ⟨w', hw'⟩
    rw [snocIt_append] at hw'
    refine ⟨Fin.init w', w' (Fin.last (n+1)), ?_⟩
    show Fin.snoc (Fin.append ξ (Fin.init w')) (w' (Fin.last (n+1))) ∈ BigSetP p n A
    rwa [← Fin.append_snoc, Fin.snoc_init_self]
  · rintro ⟨x, v, hx⟩
    refine ⟨Fin.snoc x v, ?_⟩
    rw [snocIt_append, Fin.append_snoc]
    exact hx

theorem KsetP_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (ζ : Fin (W2 p n) → ℝ) :
    ζ ∈ KsetP p n A ↔ ζ (rIdx2 p n) ≠ 0 ∧ ζ ∉ G1P p n A := by
  simp only [KsetP, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]

theorem P1P_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (ξ : Fin (W1 p n) → ℝ) :
    ξ ∈ P1P p n A ↔ ∃ ρ : ℝ, YgenP p n ξ ρ ∈ KsetP p n A := by
  simp only [P1P, projLast, YgenP, Set.mem_setOf_eq]

theorem P2P_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (ξ : Fin (W1 p n) → ℝ) :
    ξ ∈ P2P p n A ↔ ξ ∉ P1P p n A ∧ 0 < ξ (eIdx1 p n) := by
  simp only [P2P, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]

theorem BcP_mem_iff (A : Set (Fin (Wp p n) → ℝ)) (w : Fin (Wp p n) → ℝ) :
    w ∈ BcP p n A ↔ ∃ ε : ℝ, XgenP p n w ε ∈ P2P p n A := by
  simp only [BcP, projLast, XgenP, Set.mem_setOf_eq]

/-! ## 3  The semantic characterisation of `Bc` -/

theorem BcP_mem_iff' (A : Set (Fin (Wp p n) → ℝ)) (w : Fin (Wp p n) → ℝ) :
    w ∈ BcP p n A ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ ρ : ℝ, ρ ≠ 0 → ∃ (x : Fin (n+1) → ℝ) (v : ℝ),
      Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) x) v ∈ A ∧
      (∀ j, (x j - Work.WilkG4c.cubePt (Fin.init w) j) ^ 2 ≤ ρ ^ 2) ∧
      x ≠ Work.WilkG4c.cubePt (Fin.init w) ∧
      ε ^ 2 < (v - w (Fin.last (p + (n+1)))) ^ 2 := by
  rw [BcP_mem_iff]
  constructor
  · rintro ⟨ε, hε⟩
    rw [P2P_mem_iff] at hε
    obtain ⟨hε1, hε2⟩ := hε
    rw [XgenP_e] at hε2
    refine ⟨ε, hε2, fun ρ hρ => ?_⟩
    rw [P1P_mem_iff, not_exists] at hε1
    have hg : YgenP p n (XgenP p n w ε) ρ ∈ G1P p n A := by
      have h := hε1 ρ
      rw [KsetP_mem_iff, YgenP_r] at h
      exact of_not_not fun hc => h ⟨hρ, hc⟩
    rw [G1P_mem_iff] at hg
    obtain ⟨x, v, hx⟩ := hg
    rw [BigSetP_mem_iff] at hx
    obtain ⟨hA, _h1, _h2, h3, h4, h5⟩ := hx
    refine ⟨x, v, ?_, ?_, ?_, ?_⟩
    · rwa [ZgenP_pullbackP] at hA
    · intro j
      simpa only [ZgenP_y, ZgenP_y0, YgenP_y0, XgenP_y0, ZgenP_r, YgenP_r, cubePt_y0IdxW]
        using h3 j
    · intro hxeq
      obtain ⟨j, hj⟩ := h4
      exact hj (by
        simpa only [ZgenP_y, ZgenP_y0, YgenP_y0, XgenP_y0, cubePt_y0IdxW]
          using congrFun hxeq j)
    · simpa only [ZgenP_v, ZgenP_v0, YgenP_v0, XgenP_v0, ZgenP_e, YgenP_e, XgenP_e,
        v0IdxW_eq] using h5
  · rintro ⟨ε, hε0, hP⟩
    refine ⟨ε, ?_⟩
    rw [P2P_mem_iff]
    refine ⟨?_, by rw [XgenP_e]; exact hε0⟩
    rw [P1P_mem_iff, not_exists]
    intro ρ
    rw [KsetP_mem_iff, YgenP_r]
    rintro ⟨hρ, hnotG⟩
    obtain ⟨x, v, hA, h3, h4, h5⟩ := hP ρ hρ
    exact hnotG (by
      rw [G1P_mem_iff]
      refine ⟨x, v, ?_⟩
      rw [BigSetP_mem_iff]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rwa [ZgenP_pullbackP]
      · simpa only [ZgenP_e, YgenP_e, XgenP_e] using hε0
      · rw [ZgenP_r, YgenP_r]; exact hρ
      · intro j
        simpa only [ZgenP_y, ZgenP_y0, YgenP_y0, XgenP_y0, ZgenP_r, YgenP_r, cubePt_y0IdxW]
          using h3 j
      · by_contra hcon
        refine h4 ?_
        funext j
        by_contra hj
        exact hcon ⟨j, by
          simpa only [ZgenP_y, ZgenP_y0, YgenP_y0, XgenP_y0, cubePt_y0IdxW] using hj⟩
      · simpa only [ZgenP_v, ZgenP_v0, YgenP_v0, XgenP_v0, ZgenP_e, YgenP_e, XgenP_e,
          v0IdxW_eq] using h5)

theorem BcP_eq_CoreP (A : Set (Fin (Wp p n) → ℝ)) : BcP p n A = CoreP p n A := by
  ext w
  rw [BcP_mem_iff']
  rfl

/-! ## 4  `Core` versus the fibre-limit set -/

theorem CoreP_compl_eq (A : Set (Fin (Wp p n) → ℝ)) : (CoreP p n A)ᶜ = LimeqP p n A := by
  ext w
  simp only [CoreP, LimeqP, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · intro h ε hε
    have h1 : ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ (x : Fin (n+1) → ℝ) (v : ℝ),
        ¬(Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) x) v ∈ A ∧
          (∀ j, (x j - Work.WilkG4c.cubePt (Fin.init w) j) ^ 2 ≤ ρ ^ 2) ∧
          x ≠ Work.WilkG4c.cubePt (Fin.init w) ∧
          ε ^ 2 < (v - w (Fin.last (p + (n+1)))) ^ 2) := by
      by_contra hc
      apply h
      refine ⟨ε, hε, fun ρ hρ => ?_⟩
      by_contra hc2
      exact hc ⟨ρ, hρ, fun x v hcon => hc2 ⟨x, v, hcon⟩⟩
    obtain ⟨ρ, hρ0, hρ2⟩ := h1
    refine ⟨|ρ|, abs_pos.mpr hρ0, ?_⟩
    intro x hx hxd v hv
    have hsq : ∀ j, (x j - Work.WilkG4c.cubePt (Fin.init w) j) ^ 2 ≤ ρ ^ 2 := by
      intro j
      have hlt : |x j - Work.WilkG4c.cubePt (Fin.init w) j| < |ρ| := hxd j
      calc (x j - Work.WilkG4c.cubePt (Fin.init w) j) ^ 2
          = |x j - Work.WilkG4c.cubePt (Fin.init w) j| ^ 2 := (sq_abs _).symm
        _ ≤ |ρ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hlt) 2
        _ = ρ ^ 2 := sq_abs ρ
    have hge : ¬(ε ^ 2 < (v - w (Fin.last (p + (n+1)))) ^ 2) :=
      fun hlt => hρ2 x v ⟨hv, hsq, hx, hlt⟩
    exact abs_le_of_sq_le_sq (le_of_not_gt hge) (le_of_lt hε)
  · intro h
    rintro ⟨ε, hε, hP⟩
    obtain ⟨δ, hδ0, hδ⟩ := h ε hε
    obtain ⟨x, v, hf, hsq, hx, hlt⟩ := hP (δ / 2)
      (ne_of_gt (by linarith : (0 : ℝ) < δ / 2))
    have hbd : ∀ j, |x j - Work.WilkG4c.cubePt (Fin.init w) j| ≤ δ / 2 := by
      intro j
      have hh := sq_le_sq.mp (hsq j)
      rwa [abs_of_pos (by linarith : (0 : ℝ) < δ / 2)] at hh
    have h1 : ∀ j, |x j - Work.WilkG4c.cubePt (Fin.init w) j| < δ :=
      fun j => by linarith [hbd j]
    have hle := hδ x hx h1 v hf
    have h2 : (v - w (Fin.last (p + (n+1)))) ^ 2 ≤ ε ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_pos hε]; exact hle)
    linarith

theorem BsetP_eq_LimeqP (A : Set (Fin (Wp p n) → ℝ)) : BsetP p n A = LimeqP p n A := by
  rw [BsetP, BcP_eq_CoreP, CoreP_compl_eq]

end Work.WilG4c
