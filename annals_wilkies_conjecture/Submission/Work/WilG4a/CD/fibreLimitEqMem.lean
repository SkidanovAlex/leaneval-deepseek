import Mathlib
import Submission.Work.WilG4a.CD.fibLimDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## §10  The core description of `Bc` -/

/-- The `∃ε ∀ρ ∃t v` description of `Bc`. -/
def Core (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+2) → ℝ) :=
  {w | ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, r ≠ 0 → ∃ t v : ℝ,
    fibre_y p w t v ∈ A ∧ (t - w (yIdx2 p)) ^ 2 ≤ r ^ 2 ∧ t ≠ w (yIdx2 p) ∧
    ε ^ 2 < (v - w (v0Idx2 p)) ^ 2}

theorem Bc_eq_Core (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Bc p A = Core p A := by
  ext w
  rw [Bc_mem_iff]
  simp only [Core, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ε, hεP2⟩
    rw [P2_mem_iff] at hεP2
    obtain ⟨hnotP1, hεpos⟩ := hεP2
    rw [Xgen_e] at hεpos
    refine ⟨ε, hεpos, ?_⟩
    intro r hr
    have hK : ¬(Ygen p (Xgen p w ε) r ∈ Kset p A) :=
      fun hc => hnotP1 ((P1_mem_iff p A (Xgen p w ε)).mpr ⟨r, hc⟩)
    rw [Kset_mem_iff] at hK
    have hG1 : Ygen p (Xgen p w ε) r ∈ G1 p A := by
      by_contra hc
      exact hK ⟨by rwa [Ygen_r], hc⟩
    rw [G1_mem_iff] at hG1
    obtain ⟨t, v, hA, _h1, _h2, h3, h4, h5⟩ := hG1
    refine ⟨t, v, ?_, ?_, ?_, ?_⟩
    · rw [fibre_eq, ← pre3_Xgen p w ε, ← pre4_Ygen p (Xgen p w ε) r]; exact hA
    · have hh := h3; rw [Ygen_y, Xgen_y, Ygen_r] at hh; exact hh
    · have hh := h4; rw [Ygen_y, Xgen_y] at hh; exact hh
    · have hh := h5; rw [Ygen_e, Xgen_e, Ygen_v0, Xgen_v0] at hh; exact hh
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, ?_⟩
    rw [P2_mem_iff]
    refine ⟨?_, by rw [Xgen_e]; exact hε⟩
    rw [P1_mem_iff, not_exists]
    intro r
    rw [Kset_mem_iff]
    rintro ⟨hr0, hG1not⟩
    rw [Ygen_r] at hr0
    rw [G1_mem_iff] at hG1not
    obtain ⟨t, v, h1, h2⟩ := h r hr0
    apply hG1not
    refine ⟨t, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pre4_Ygen, pre3_Xgen, ← fibre_eq]; exact h1
    · rw [Ygen_e, Xgen_e]; exact hε
    · rw [Ygen_r]; exact hr0
    · rw [Ygen_y, Xgen_y, Ygen_r]; exact h2.1
    · rw [Ygen_y, Xgen_y]; exact h2.2.1
    · rw [Ygen_e, Xgen_e, Ygen_v0, Xgen_v0]; exact h2.2.2

/-! ## §11  The fibre_y-limit description -/

/-- The fibre_y-limit set of the statement. -/
def LimSet (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : Set (Fin (p+2) → ℝ) :=
  {w | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) → |t - (Fin.init w) (Fin.last p)| < δ →
      ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
        |v - w (Fin.last (p+1))| ≤ ε}

theorem Core_compl_eq (p : ℕ) (A : Set (Fin (p+2) → ℝ)) : (Core p A)ᶜ = LimSet p A := by
  ext w
  simp only [Set.mem_compl_iff, Core, LimSet, Set.mem_ofPred_eq]
  constructor
  · -- not `∃ε>0 ∀ρ≠0 ∃t v`  ⟹  the `∀ε ∃δ` condition
    intro h ε hε
    have h1 : ∃ r : ℝ, r ≠ 0 ∧ ∀ t v : ℝ,
        ¬(fibre_y p w t v ∈ A ∧ (t - w (yIdx2 p)) ^ 2 ≤ r ^ 2 ∧ t ≠ w (yIdx2 p) ∧
          ε ^ 2 < (v - w (v0Idx2 p)) ^ 2) := by
      by_contra hc
      apply h
      refine ⟨ε, hε, fun r hr => ?_⟩
      by_contra hc2
      exact hc ⟨r, hr, fun t v hcon => hc2 ⟨t, v, hcon⟩⟩
    obtain ⟨r, hr0, hr2⟩ := h1
    refine ⟨|r|, abs_pos.mpr hr0, ?_⟩
    intro t ht htd v hv
    have hsq : (t - w (yIdx2 p)) ^ 2 ≤ r ^ 2 := by
      have hlt : |t - w (yIdx2 p)| < |r| := by rwa [init_last p w] at htd
      calc (t - w (yIdx2 p)) ^ 2 = |t - w (yIdx2 p)| ^ 2 := (sq_abs _).symm
        _ ≤ |r| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hlt) 2
        _ = r ^ 2 := sq_abs r
    have hne : t ≠ w (yIdx2 p) := by rwa [init_last p w] at ht
    have hge : ¬(ε ^ 2 < (v - w (v0Idx2 p)) ^ 2) :=
      fun hlt => hr2 t v ⟨hv, hsq, hne, hlt⟩
    have habs : |v - w (v0Idx2 p)| ≤ ε :=
      abs_le_of_sq_le_sq (le_of_not_gt hge) (le_of_lt hε)
    rw [last_eq p w]
    exact habs
  · -- the `∀ε ∃δ` condition  ⟹  not `∃ε>0 ∀ρ≠0 ∃t v`
    intro h
    rintro ⟨ε, hε, hP⟩
    obtain ⟨δ, hδ0, hδ⟩ := h ε hε
    obtain ⟨t, v, hf, hsq, hne, hlt⟩ := hP (δ / 2)
      (ne_of_gt (by linarith : (0 : ℝ) < δ / 2))
    have hbd : |t - w (yIdx2 p)| ≤ δ / 2 := by
      have hh := sq_le_sq.mp hsq
      rwa [abs_of_pos (by linarith : (0 : ℝ) < δ / 2)] at hh
    have h1 : |t - (Fin.init w) (Fin.last p)| < δ := by
      rw [init_last p w]
      linarith
    have hne' : t ≠ (Fin.init w) (Fin.last p) := by rwa [← init_last p w] at hne
    have hle := hδ t hne' h1 v hf
    have h2 : (v - w (Fin.last (p+1))) ^ 2 ≤ ε ^ 2 := by
      have h3 : |v - w (Fin.last (p+1))| ≤ |ε| := by rwa [abs_of_pos hε]
      exact sq_le_sq.mpr h3
    rw [← last_eq p w] at hlt
    linarith

/-! ## §12  Assembly -/

theorem rIdx4_ne_mem (S : SOMin) (p : ℕ) :
    {ζ : Fin (p+4) → ℝ | ζ (rIdx4 p) ≠ 0} ∈ S.Ω (p+5) 1 (p+4) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (p+4)
    (MvPolynomial.X (rIdx4 p) : MvPolynomial (Fin (p+4)) ℝ)
  rw [show {x : Fin (p+4) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (rIdx4 p) : MvPolynomial (Fin (p+4)) ℝ) ≠ 0}
      = {ζ : Fin (p+4) → ℝ | ζ (rIdx4 p) ≠ 0} from by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  exact le_of_eq (MvPolynomial.totalDegree_X (rIdx4 p))

theorem eIdx3_pos_mem (S : SOMin) (p : ℕ) :
    {ξ : Fin (p+3) → ℝ | 0 < ξ (eIdx3 p)} ∈ S.Ω (p+6) 3 (p+3) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (p+3)
    (-MvPolynomial.X (eIdx3 p) : MvPolynomial (Fin (p+3)) ℝ)
  rw [show {x : Fin (p+3) → ℝ |
        MvPolynomial.eval x (-MvPolynomial.X (eIdx3 p) : MvPolynomial (Fin (p+3)) ℝ) < 0}
      = {ξ : Fin (p+3) → ℝ | 0 < ξ (eIdx3 p)} from by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
    exact neg_lt_zero] at h
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have := td_negX_le (eIdx3 p); omega

theorem Bset_mem {S : SOMin} {p F D : ℕ} {A : Set (Fin (p+2) → ℝ)}
    (hA : A ∈ S.Ω F D (p+2)) :
    Bset p A ∈ S.Ω (F + 4 * p + 31) (D + 19) (p + 2) := by
  have hBig := BigSet_mem (S := S) (p := p) hA
  have hG1 : G1 p A ∈ S.Ω (F + 4 * p + 24) (D + 15) (p + 4) := by
    have h1 : projLast (BigSet p A) ∈ S.Ω (F + 4 * p + 23) (D + 15) (p + 5) :=
      Work.WilG1.Omega.mono (S.proj hBig) (by omega) le_rfl
    have h2 : projLast (projLast (BigSet p A)) ∈ S.Ω (F + 4 * p + 24) (D + 15) (p + 4) :=
      Work.WilG1.Omega.mono (S.proj h1) (by omega) le_rfl
    exact h2
  have hK : Kset p A ∈ S.Ω (F + 4 * p + 26) (D + 16) (p + 4) := by
    have hG1c : (G1 p A)ᶜ ∈ S.Ω (F + 4 * p + 25) (D + 15) (p + 4) :=
      Work.WilG1.Omega.mono (S.compl hG1) (by omega) le_rfl
    have hrne : {ζ : Fin (p+4) → ℝ | ζ (rIdx4 p) ≠ 0} ∈ S.Ω (F + 4 * p + 25) 1 (p + 4) :=
      Work.WilG1.Omega.mono (rIdx4_ne_mem S p) (by omega) le_rfl
    simp only [Kset]
    exact Work.WilG1.Omega.mono (inter2_same (S := S) hrne hG1c) (by omega) (by omega)
  have hP1 : P1 p A ∈ S.Ω (F + 4 * p + 27) (D + 16) (p + 3) := by
    have := S.proj hK
    exact Work.WilG1.Omega.mono this (by omega) le_rfl
  have hP2 : P2 p A ∈ S.Ω (F + 4 * p + 29) (D + 19) (p + 3) := by
    have hP1c : (P1 p A)ᶜ ∈ S.Ω (F + 4 * p + 28) (D + 16) (p + 3) :=
      Work.WilG1.Omega.mono (S.compl hP1) (by omega) le_rfl
    have hposE : {ξ : Fin (p+3) → ℝ | 0 < ξ (eIdx3 p)} ∈ S.Ω (F + 4 * p + 28) 3 (p + 3) :=
      Work.WilG1.Omega.mono (eIdx3_pos_mem S p) (by omega) le_rfl
    simp only [P2]
    exact Work.WilG1.Omega.mono (inter2_same (S := S) hP1c hposE) (by omega) (by omega)
  have hBc : Bc p A ∈ S.Ω (F + 4 * p + 30) (D + 19) (p + 2) := by
    have := S.proj hP2
    exact Work.WilG1.Omega.mono this (by omega) le_rfl
  have hBset : Bset p A ∈ S.Ω (F + 4 * p + 31) (D + 19) (p + 2) := by
    simp only [Bset]
    exact Work.WilG1.Omega.mono (S.compl hBc) (by omega) le_rfl
  exact hBset

/-- Parametrised `Ω`-construction: for an `Ω`-set `A ⊆ ℝ^{p+2}`, the set of points
`w : Fin (p+2) → ℝ` (with `z := Fin.init w` and value `w (Fin.last (p+1))`) such that the
`A`-values along the fibre_y `t ↦ (Fin.init z, t, ·)` tend to `w (Fin.last (p+1))` as `t` tends to
`z (Fin.last p)`, is `Ω`-definable with format exceeding the atom's by a fixed amount and
degree a fixed polynomial in the atom's degree. -/
theorem fibreLimitEqMem {p : ℕ} {S : WilkiesDesign.SOMin} :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ {F D : ℕ} (A : Set (Fin (p + 2) → ℝ)), A ∈ S.Ω F D (p + 2) →
        {w : Fin (p + 2) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) → |t - (Fin.init w) (Fin.last p)| < δ →
            ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
              |v - w (Fin.last (p + 1))| ≤ ε} ∈
          S.Ω (F + a) (b.eval D) (p + 2) := by
  refine ⟨4 * p + 31, Polynomial.X + Polynomial.C 19, ?_⟩
  intro F D A hA
  have hmem : Bset p A ∈ S.Ω (F + 4 * p + 31) (D + 19) (p + 2) := Bset_mem (S := S) hA
  have hset : ({w : Fin (p+2) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) → |t - (Fin.init w) (Fin.last p)| < δ →
            ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
              |v - w (Fin.last (p + 1))| ≤ ε} : Set (Fin (p+2) → ℝ)) = Bset p A := by
    rw [show ({w : Fin (p+2) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) → |t - (Fin.init w) (Fin.last p)| < δ →
            ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
              |v - w (Fin.last (p + 1))| ≤ ε} : Set (Fin (p+2) → ℝ)) = LimSet p A from rfl]
    rw [← Core_compl_eq p A, ← Bc_eq_Core p A]
    rfl
  rw [hset]
  refine Work.WilG1.Omega.mono hmem le_rfl ?_
  simp [Polynomial.eval_add]

end Work.WilG4a.CD
