import Mathlib
import Submission.Work.Diff.STE.Lead.pPhi_bound_kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The explicit-constant chain of entry bounds for the DeTurck operator `pPhi`

`Work.Diff.STE.Lead.Lv dM dA dB dc K M MA MB cl x` is the degree-carrying size bound
`|x| ≤ K (1+M)^dM (1+MA)^dA (1+MB)^dB (cl⁻¹)^dc`, and `Work.Diff.STE.Lead.Hyp M MA MB cl` the
hypotheses `1 ≤ M, 1 ≤ MA, 1 ≤ MB, 0 < cl ≤ 1` (see `pPhi_bound_kit.lean` for the closure lemmas).

This file propagates *explicit* bounds — the constant of the conclusion is a closed expression in
the constants of the hypotheses, never an unspecified `∃ K`.  That is what is needed to produce the
constant of `pPhi_entry_bound_v2`, which is quantified before all the data: the assembled chain has
to be a closed real number.

The levels (degrees in `M`, `MA`, `MB`, `cl⁻¹`) are as in `pPhi_entry_bound.lean`:

| object | level | constant from |
|---|---|---|
| `jKz`, `jKzD` | `(1,0,0,0)` | `3 KL` |
| `jGamU` | `(1,0,0,1)` | `N (KI KK)` |
| `jdInv` | `(1,0,0,2)` | `N (N ((KI KI) KL))` |
| `jdGamU` | `(2,0,0,2)` | `N ((KJ KK) + (KI KD))` |
| `jRm` | `(2,0,0,1)` | `((KD+KD) + N (N ((KI KK) KK))) + N (N ((KI KK) KK))` |
| `jRic` | `(2,0,0,2)` | `N (N (KI KR))` |
| `jWU` | `(1,0,1,2)` | `N (N (KI (KG + KGb)))` |
| `jWb` | `(1,1,1,2)` | `N (KA KWU)` |
| `jdWU` | `(2,0,2,3)` | `N (N ((KJ (KG+KGb)) + ((KI KDG) + (KI KDb))))` |
| `jdWb` | `(2,1,2,3)` | `N ((KL KWU) + (KA KJW))` |
| `jnabW` | `(2,1,2,3)` | `KJ + N (KG KWB)` |
| `jLW` | `(2,1,2,3)` | `KN + KN` |

where `N = (Fintype.card (Fin (finrank ℝ E)) : ℝ)` is `idxCard E`, the factor contributed by each
sum over the index type.
-/

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.STE.Lead

open Work.Diff.EXT Work.Diff.STE.DeTurck

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- The cardinality factor `N` contributed by a sum over the index type `Fin (finrank ℝ E)`. -/
abbrev idxCard (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ℝ :=
  (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)

/-- Enlarging the constant of an `Lv` bound. -/
lemma Lv_weaken {M MA MB cl : ℝ} {dM dA dB dc : ℕ} {K K' x : ℝ}
    (h : Lv dM dA dB dc K M MA MB cl x) (hh : Hyp M MA MB cl) (hKK : K ≤ K') :
    Lv dM dA dB dc K' M MA MB cl x :=
  le_trans h (mul_le_mul_of_nonneg_right hKK (Lv.X_nonneg hh dM dA dB dc))

/-- Every entry of a matrix `f : MatE` is bounded by its norm (the sup norm on `MatE`). -/
lemma abs_entry_le_norm (f : MatE (E := E)) (i j : Fin (Module.finrank ℝ E)) : |f i j| ≤ ‖f‖ := by
  have h1 : ‖f i‖ ≤ ‖f‖ := norm_le_pi_norm f i
  have h2 : ‖f i j‖ ≤ ‖f i‖ := norm_le_pi_norm (f i) j
  rw [Real.norm_eq_abs] at h2
  exact le_trans h2 h1

/-- An entry of a foreground jet, at level `(1,0,0,0)` with constant `1`. -/
lemma Lv_entry_fg {M MA MB cl : ℝ} (hh : Hyp M MA MB cl) {f : MatE (E := E)} (hf : ‖f‖ ≤ M) :
    ∀ i j, Lv 1 0 0 0 1 M MA MB cl (f i j) := by
  intro i j
  have h1 := abs_entry_le_norm f i j
  simp only [Lv, pow_one, pow_zero, mul_one, one_mul]
  linarith [hh.hM]

/-- An entry of a background jet, at level `(0,0,1,0)` with constant `1`. -/
lemma Lv_entry_bg {M MA MB cl : ℝ} (hh : Hyp M MA MB cl) {f : MatE (E := E)} (hf : ‖f‖ ≤ MB) :
    ∀ i j, Lv 0 0 1 0 1 M MA MB cl (f i j) := by
  intro i j
  have h1 := abs_entry_le_norm f i j
  simp only [Lv, pow_one, pow_zero, mul_one, one_mul]
  linarith [hh.hB]

/-- An entry of the foreground Gram matrix, at level `(0,1,0,0)` with constant `1`. -/
lemma Lv_entry_A {M MA MB cl : ℝ} (hh : Hyp M MA MB cl) {A : MatE (E := E)}
    (hA : ∀ i j, |A i j| ≤ MA) : ∀ i j, Lv 0 1 0 0 1 M MA MB cl (A i j) := by
  intro i j
  simp only [Lv, pow_one, pow_zero, mul_one, one_mul]
  linarith [hh.hA, hA i j]

/-- An entry of the background Gram matrix, at level `(0,0,1,0)` with constant `1`. -/
lemma Lv_entry_Abar {M MA MB cl : ℝ} (hh : Hyp M MA MB cl) {A : MatE (E := E)}
    (hA : ∀ i j, |A i j| ≤ MB) : ∀ i j, Lv 0 0 1 0 1 M MA MB cl (A i j) := by
  intro i j
  simp only [Lv, pow_one, pow_zero, mul_one, one_mul]
  linarith [hh.hB, hA i j]

/-! ## The chain -/

lemma chain_jKz {M MA MB cl KL : ℝ} (hh : Hyp M MA MB cl) (hK : 0 ≤ KL) {L : LinMat E}
    (hL : ∀ a p q : Fin (Module.finrank ℝ E),
      Lv 1 0 0 0 KL M MA MB cl (L (bB (E := E) a) p q)) :
    ∀ a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 (3 * KL) M MA MB cl (jKz L a b c) := by
  intro a b c
  have h12 : Lv 1 0 0 0 (KL + KL) M MA MB cl
      (L (bB a) b c + L (bB b) a c) :=
    Lv.add (hL a b c) (hL b a c) hh hK hK
  have h123 : Lv 1 0 0 0 ((KL + KL) + KL) M MA MB cl
      (L (bB a) b c + L (bB b) a c - L (bB c) a b) :=
    Lv.sub h12 (hL c a b) hh (add_nonneg hK hK) hK
  have h := Lv.smul (1 / 2 : ℝ) h123
  refine Lv_weaken h hh ?_
  have h2 : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := abs_of_pos (by norm_num)
  rw [h2]; nlinarith

lemma chain_jKzD {M MA MB cl KB : ℝ} (hh : Hyp M MA MB cl) (hK : 0 ≤ KB) {B : BilMat E}
    (hB : ∀ m a p q : Fin (Module.finrank ℝ E),
      Lv 1 0 0 0 KB M MA MB cl (B (bB (E := E) m) (bB (E := E) a) p q)) :
    ∀ m a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 (3 * KB) M MA MB cl (jKzD B m a b c) := by
  intro m a b c
  have h12 : Lv 1 0 0 0 (KB + KB) M MA MB cl
      (B (bB m) (bB a) b c + B (bB m) (bB b) a c) :=
    Lv.add (hB m a b c) (hB m b a c) hh hK hK
  have h123 : Lv 1 0 0 0 ((KB + KB) + KB) M MA MB cl
      (B (bB m) (bB a) b c + B (bB m) (bB b) a c - B (bB m) (bB c) a b) :=
    Lv.sub h12 (hB m c a b) hh (add_nonneg hK hK) hK
  have h := Lv.smul (1 / 2 : ℝ) h123
  refine Lv_weaken h hh ?_
  have h2 : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := abs_of_pos (by norm_num)
  rw [h2]; nlinarith

lemma chain_jGamU {M MA MB cl KI KK : ℝ} (hh : Hyp M MA MB cl) (hI : 0 ≤ KI) (hK : 0 ≤ KK)
    {A : MatE (E := E)} {L : LinMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hKz : ∀ a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 KK M MA MB cl (jKz L a b c)) :
    ∀ r a b : Fin (Module.finrank ℝ E),
      Lv 1 0 0 1 (idxCard E * (KI * KK)) M MA MB cl (jGamU A L r a b) := by
  intro r a b
  exact Lv.sum (fun p => Lv.mul (hInv r p) (hKz a b p) hh hI hK) hh (mul_nonneg hI hK)

lemma chain_jdInv {M MA MB cl KI KL : ℝ} (hh : Hyp M MA MB cl) (hI : 0 ≤ KI) (hK : 0 ≤ KL)
    {A : MatE (E := E)} {L : LinMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hL : ∀ a p q : Fin (Module.finrank ℝ E),
      Lv 1 0 0 0 KL M MA MB cl (L (bB (E := E) a) p q)) :
    ∀ a i j : Fin (Module.finrank ℝ E),
      Lv 1 0 0 2 (idxCard E * (idxCard E * ((KI * KI) * KL))) M MA MB cl (jdInv A L a i j) := by
  intro a i j
  refine Lv.neg ?_
  refine Lv.sum (fun p => ?_) hh ?_
  · refine Lv.sum (fun q => ?_) hh ?_
    · exact Lv.mul (Lv.mul (hInv i p) (hInv j q) hh hI hI) (hL a p q) hh
        (mul_nonneg hI hI) hK
    · positivity
  · positivity

lemma chain_jdGamU {M MA MB cl KI KK KD KJ : ℝ} (hh : Hyp M MA MB cl)
    (hI : 0 ≤ KI) (hK : 0 ≤ KK) (hD : 0 ≤ KD) (hJ : 0 ≤ KJ)
    {A : MatE (E := E)} {L : LinMat E} {B : BilMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hKz : ∀ a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 KK M MA MB cl (jKz L a b c))
    (hKzD : ∀ m a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 KD M MA MB cl (jKzD B m a b c))
    (hjdInv : ∀ a i j : Fin (Module.finrank ℝ E),
      Lv 1 0 0 2 KJ M MA MB cl (jdInv A L a i j)) :
    ∀ a r i j : Fin (Module.finrank ℝ E),
      Lv 2 0 0 2 (idxCard E * ((KJ * KK) + (KI * KD))) M MA MB cl (jdGamU A L B a r i j) := by
  intro a r i j
  refine Lv.sum (fun p => ?_) hh ?_
  · exact Lv.add (Lv.mul (hjdInv a r p) (hKz i j p) hh hJ hK)
      (Lv.mono (Lv.mul (hInv r p) (hKzD a i j p) hh hI hD) hh (mul_nonneg hI hD)
        (by omega) (by omega) (by omega) (by omega))
      hh (mul_nonneg hJ hK) (mul_nonneg hI hD)
  · positivity

lemma chain_jRm {M MA MB cl KI KK KD : ℝ} (hh : Hyp M MA MB cl)
    (hI : 0 ≤ KI) (hK : 0 ≤ KK) (hD : 0 ≤ KD)
    {A : MatE (E := E)} {L : LinMat E} {B : BilMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hKz : ∀ a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 KK M MA MB cl (jKz L a b c))
    (hKzD : ∀ m a b c : Fin (Module.finrank ℝ E), Lv 1 0 0 0 KD M MA MB cl (jKzD B m a b c)) :
    ∀ a b c d : Fin (Module.finrank ℝ E),
      Lv 2 0 0 1 ((KD + KD) + (idxCard E * (idxCard E * ((KI * KK) * KK)))
        + (idxCard E * (idxCard E * ((KI * KK) * KK)))) M MA MB cl (jRm A L B a b c d) := by
  intro a b c d
  have hsub : Lv 1 0 0 0 (KD + KD) M MA MB cl (jKzD B a d b c - jKzD B b d a c) :=
    Lv.sub (hKzD a d b c) (hKzD b d a c) hh hD hD
  have hs : ∀ (x y p q : Fin (Module.finrank ℝ E)),
      Lv 2 0 0 1 (idxCard E * (idxCard E * ((KI * KK) * KK))) M MA MB cl
        (∑ r, ∑ s, jInv A r s * jKz L x y r * jKz L p q s) := by
    intro x y p q
    refine Lv.sum (fun r => ?_) hh ?_
    · refine Lv.sum (fun s => ?_) hh ?_
      · exact Lv.mul (Lv.mul (hInv r s) (hKz x y r) hh hI hK) (hKz p q s) hh
          (mul_nonneg hI hK) hK
      · positivity
    · positivity
  have h1 : Lv 2 0 0 1 ((KD + KD) + idxCard E * (idxCard E * ((KI * KK) * KK)))
      M MA MB cl (jKzD B a d b c - jKzD B b d a c
        - (∑ r, ∑ s, jInv A r s * jKz L d b r * jKz L a c s)) :=
    Lv.sub (Lv.mono hsub hh (add_nonneg hD hD) (by omega) (by omega) (by omega) (by omega))
      (hs d b a c) hh (add_nonneg hD hD) (by positivity)
  exact Lv.add h1 (hs d a b c) hh (by positivity) (by positivity)

lemma chain_jRic {M MA MB cl KI KR : ℝ} (hh : Hyp M MA MB cl) (hI : 0 ≤ KI) (hR : 0 ≤ KR)
    {A : MatE (E := E)} {L : LinMat E} {B : BilMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hRm : ∀ a b c d : Fin (Module.finrank ℝ E),
      Lv 2 0 0 1 KR M MA MB cl (jRm A L B a b c d)) :
    ∀ i j : Fin (Module.finrank ℝ E),
      Lv 2 0 0 2 (idxCard E * (idxCard E * (KI * KR))) M MA MB cl (jRic A L B i j) := by
  intro i j
  refine Lv.sum (fun k => ?_) hh ?_
  · refine Lv.sum (fun l => ?_) hh ?_
    · exact Lv.mul (hInv k l) (hRm k i l j) hh hI hR
    · positivity
  · positivity

lemma chain_jWU {M MA MB cl KI KG KGb : ℝ} (hh : Hyp M MA MB cl)
    (hI : 0 ≤ KI) (hG : 0 ≤ KG) (hGb : 0 ≤ KGb)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hGam : ∀ r a b : Fin (Module.finrank ℝ E), Lv 1 0 0 1 KG M MA MB cl (jGamU A L r a b))
    (hGamb : ∀ r a b : Fin (Module.finrank ℝ E),
      Lv 0 0 1 1 KGb M MA MB cl (jGamU Abar Lbar r a b)) :
    ∀ k : Fin (Module.finrank ℝ E),
      Lv 1 0 1 2 (idxCard E * (idxCard E * (KI * (KG + KGb)))) M MA MB cl
        (jWU A L Abar Lbar k) := by
  intro k
  refine Lv.sum (fun i => ?_) hh ?_
  · refine Lv.sum (fun j => ?_) hh ?_
    · exact Lv.mul (hInv i j)
        (Lv.submax (hGam k i j) (hGamb k i j) hh hG hGb) hh hI (add_nonneg hG hGb)
    · positivity
  · positivity

lemma chain_jWb {M MA MB cl KA KW : ℝ} (hh : Hyp M MA MB cl) (hA : 0 ≤ KA) (hW : 0 ≤ KW)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E}
    (hAe : ∀ i j : Fin (Module.finrank ℝ E), Lv 0 1 0 0 KA M MA MB cl (A i j))
    (hWU : ∀ k : Fin (Module.finrank ℝ E),
      Lv 1 0 1 2 KW M MA MB cl (jWU A L Abar Lbar k)) :
    ∀ b : Fin (Module.finrank ℝ E),
      Lv 1 1 1 2 (idxCard E * (KA * KW)) M MA MB cl (jWb A L Abar Lbar b) := by
  intro b
  exact Lv.sum (fun c => Lv.mul (hAe b c) (hWU c) hh hA hW) hh (mul_nonneg hA hW)

lemma chain_jdWU {M MA MB cl KI KJ KG KGb KDG KDb : ℝ} (hh : Hyp M MA MB cl)
    (hI : 0 ≤ KI) (hJ : 0 ≤ KJ) (hG : 0 ≤ KG) (hGb : 0 ≤ KGb) (hDG : 0 ≤ KDG) (hDb : 0 ≤ KDb)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E} {B Bbar : BilMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hjdInv : ∀ a i j : Fin (Module.finrank ℝ E),
      Lv 1 0 0 2 KJ M MA MB cl (jdInv A L a i j))
    (hGam : ∀ r a b : Fin (Module.finrank ℝ E), Lv 1 0 0 1 KG M MA MB cl (jGamU A L r a b))
    (hGamb : ∀ r a b : Fin (Module.finrank ℝ E),
      Lv 0 0 1 1 KGb M MA MB cl (jGamU Abar Lbar r a b))
    (hjdGam : ∀ a r i j : Fin (Module.finrank ℝ E),
      Lv 2 0 0 2 KDG M MA MB cl (jdGamU A L B a r i j))
    (hjdGamb : ∀ a r i j : Fin (Module.finrank ℝ E),
      Lv 0 0 2 2 KDb M MA MB cl (jdGamU Abar Lbar Bbar a r i j)) :
    ∀ a c : Fin (Module.finrank ℝ E),
      Lv 2 0 2 3 (idxCard E * (idxCard E * ((KJ * (KG + KGb) + KI * KDG) + KI * KDb)))
        M MA MB cl (jdWU A L B Abar Lbar Bbar a c) := by
  intro a c
  rw [jdWU]
  have houter : ∀ i : Fin (Module.finrank ℝ E),
      Lv 2 0 2 3 (idxCard E * ((KJ * (KG + KGb) + KI * KDG) + KI * KDb)) M MA MB cl
        (∑ j, (jdInv A L a i j * (jGamU A L c i j - jGamU Abar Lbar c i j)
          + jInv A i j * jdGamU A L B a c i j
          - jInv A i j * jdGamU Abar Lbar Bbar a c i j)) := by
    intro i
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        Lv 2 0 2 3 ((KJ * (KG + KGb) + KI * KDG) + KI * KDb) M MA MB cl
          (jdInv A L a i j * (jGamU A L c i j - jGamU Abar Lbar c i j)
            + jInv A i j * jdGamU A L B a c i j
            - jInv A i j * jdGamU Abar Lbar Bbar a c i j) := by
      intro j
      have ht1 : Lv 2 0 1 3 (KJ * (KG + KGb)) M MA MB cl
          (jdInv A L a i j * (jGamU A L c i j - jGamU Abar Lbar c i j)) :=
        Lv.mul (hjdInv a i j) (Lv.submax (hGam c i j) (hGamb c i j) hh hG hGb) hh hJ
          (add_nonneg hG hGb)
      have ht2 : Lv 2 0 0 3 (KI * KDG) M MA MB cl (jInv A i j * jdGamU A L B a c i j) :=
        Lv.mul (hInv i j) (hjdGam a c i j) hh hI hDG
      have ht3 : Lv 0 0 2 3 (KI * KDb) M MA MB cl
          (jInv A i j * jdGamU Abar Lbar Bbar a c i j) :=
        Lv.mul (hInv i j) (hjdGamb a c i j) hh hI hDb
      exact Lv.submax (Lv.addmax ht1 ht2 hh (mul_nonneg hJ (add_nonneg hG hGb))
        (mul_nonneg hI hDG)) ht3 hh
        (add_nonneg (mul_nonneg hJ (add_nonneg hG hGb)) (mul_nonneg hI hDG))
        (mul_nonneg hI hDb)
    exact Lv.sum hinner hh (by positivity)
  exact Lv.sum houter hh (by positivity)

lemma chain_jdWb {M MA MB cl KL KW KA KJ : ℝ} (hh : Hyp M MA MB cl)
    (hL : 0 ≤ KL) (hW : 0 ≤ KW) (hA : 0 ≤ KA) (hJ : 0 ≤ KJ)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E} {B Bbar : BilMat E}
    (hLe : ∀ a p q : Fin (Module.finrank ℝ E),
      Lv 1 0 0 0 KL M MA MB cl (L (bB (E := E) a) p q))
    (hAe : ∀ i j : Fin (Module.finrank ℝ E), Lv 0 1 0 0 KA M MA MB cl (A i j))
    (hWU : ∀ k : Fin (Module.finrank ℝ E),
      Lv 1 0 1 2 KW M MA MB cl (jWU A L Abar Lbar k))
    (hjdWU : ∀ a c : Fin (Module.finrank ℝ E),
      Lv 2 0 2 3 KJ M MA MB cl (jdWU A L B Abar Lbar Bbar a c)) :
    ∀ a b : Fin (Module.finrank ℝ E),
      Lv 2 1 2 3 (idxCard E * ((KL * KW) + (KA * KJ))) M MA MB cl
        (jdWb A L B Abar Lbar Bbar a b) := by
  intro a b
  refine Lv.sum (fun c => ?_) hh ?_
  · exact Lv.addmax (Lv.mul (hLe a b c) (hWU c) hh hL hW)
      (Lv.mul (hAe b c) (hjdWU a c) hh hA hJ) hh (mul_nonneg hL hW) (mul_nonneg hA hJ)
  · positivity

lemma chain_jnabW {M MA MB cl KJ KG KWB : ℝ} (hh : Hyp M MA MB cl)
    (hJ : 0 ≤ KJ) (hG : 0 ≤ KG) (hWB : 0 ≤ KWB)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E} {B Bbar : BilMat E}
    (hjdWb : ∀ a b : Fin (Module.finrank ℝ E),
      Lv 2 1 2 3 KJ M MA MB cl (jdWb A L B Abar Lbar Bbar a b))
    (hGam : ∀ r a b : Fin (Module.finrank ℝ E), Lv 1 0 0 1 KG M MA MB cl (jGamU A L r a b))
    (hWb : ∀ b : Fin (Module.finrank ℝ E),
      Lv 1 1 1 2 KWB M MA MB cl (jWb A L Abar Lbar b)) :
    ∀ a b : Fin (Module.finrank ℝ E),
      Lv 2 1 2 3 (KJ + idxCard E * (KG * KWB)) M MA MB cl
        (jnabW A L B Abar Lbar Bbar a b) := by
  intro a b
  have hsum : Lv 2 1 2 3 (idxCard E * (KG * KWB)) M MA MB cl
      (∑ c, jGamU A L c a b * jWb A L Abar Lbar c) :=
    Lv.mono (Lv.sum (fun c => Lv.mul (hGam c a b) (hWb c) hh hG hWB) hh
      (mul_nonneg hG hWB)) hh (by positivity)
      (by omega) (by omega) (by omega) (by omega)
  exact Lv.sub (hjdWb a b) hsum hh hJ (by positivity)

lemma chain_jLW {M MA MB cl KN : ℝ} (hh : Hyp M MA MB cl) (hN : 0 ≤ KN)
    {A Abar : MatE (E := E)} {L Lbar : LinMat E} {B Bbar : BilMat E}
    (hNab : ∀ a b : Fin (Module.finrank ℝ E),
      Lv 2 1 2 3 KN M MA MB cl (jnabW A L B Abar Lbar Bbar a b)) :
    ∀ a b : Fin (Module.finrank ℝ E),
      Lv 2 1 2 3 (KN + KN) M MA MB cl (jLW A L B Abar Lbar Bbar a b) := by
  intro a b
  exact Lv.add (hNab a b) (hNab b a) hh hN hN

/-- `jKz` on the background first jet, at level `(0,0,1,0)`. -/
lemma chain_jKz_bg {M MA MB cl KL : ℝ} (hh : Hyp M MA MB cl) (hK : 0 ≤ KL) {L : LinMat E}
    (hL : ∀ a p q : Fin (Module.finrank ℝ E),
      Lv 0 0 1 0 KL M MA MB cl (L (bB (E := E) a) p q)) :
    ∀ a b c : Fin (Module.finrank ℝ E), Lv 0 0 1 0 (3 * KL) M MA MB cl (jKz L a b c) := by
  intro a b c
  have h12 : Lv 0 0 1 0 (KL + KL) M MA MB cl
      (L (bB a) b c + L (bB b) a c) :=
    Lv.add (hL a b c) (hL b a c) hh hK hK
  have h123 : Lv 0 0 1 0 ((KL + KL) + KL) M MA MB cl
      (L (bB a) b c + L (bB b) a c - L (bB c) a b) :=
    Lv.sub h12 (hL c a b) hh (add_nonneg hK hK) hK
  have h := Lv.smul (1 / 2 : ℝ) h123
  refine Lv_weaken h hh ?_
  have h2 : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := abs_of_pos (by norm_num)
  rw [h2]; nlinarith

/-- `jKzD` on the background second jet, at level `(0,0,1,0)`. -/
lemma chain_jKzD_bg {M MA MB cl KB : ℝ} (hh : Hyp M MA MB cl) (hK : 0 ≤ KB) {B : BilMat E}
    (hB : ∀ m a p q : Fin (Module.finrank ℝ E),
      Lv 0 0 1 0 KB M MA MB cl (B (bB (E := E) m) (bB (E := E) a) p q)) :
    ∀ m a b c : Fin (Module.finrank ℝ E), Lv 0 0 1 0 (3 * KB) M MA MB cl (jKzD B m a b c) := by
  intro m a b c
  have h12 : Lv 0 0 1 0 (KB + KB) M MA MB cl
      (B (bB m) (bB a) b c + B (bB m) (bB b) a c) :=
    Lv.add (hB m a b c) (hB m b a c) hh hK hK
  have h123 : Lv 0 0 1 0 ((KB + KB) + KB) M MA MB cl
      (B (bB m) (bB a) b c + B (bB m) (bB b) a c - B (bB m) (bB c) a b) :=
    Lv.sub h12 (hB m c a b) hh (add_nonneg hK hK) hK
  have h := Lv.smul (1 / 2 : ℝ) h123
  refine Lv_weaken h hh ?_
  have h2 : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := abs_of_pos (by norm_num)
  rw [h2]; nlinarith

/-- The Christoffel symbol of the background metric, at level `(0,0,1,1)`. -/
lemma chain_jGamU_bg {M MA MB cl KI KK : ℝ} (hh : Hyp M MA MB cl) (hI : 0 ≤ KI) (hK : 0 ≤ KK)
    {A : MatE (E := E)} {L : LinMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hKz : ∀ a b c : Fin (Module.finrank ℝ E), Lv 0 0 1 0 KK M MA MB cl (jKz L a b c)) :
    ∀ r a b : Fin (Module.finrank ℝ E),
      Lv 0 0 1 1 (idxCard E * (KI * KK)) M MA MB cl (jGamU A L r a b) := by
  intro r a b
  exact Lv.sum (fun p => Lv.mul (hInv r p) (hKz a b p) hh hI hK) hh (mul_nonneg hI hK)

/-- The derivative of the inverse background Gram matrix, at level `(0,0,1,2)`. -/
lemma chain_jdInv_bg {M MA MB cl KI KL : ℝ} (hh : Hyp M MA MB cl) (hI : 0 ≤ KI) (hK : 0 ≤ KL)
    {A : MatE (E := E)} {L : LinMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hL : ∀ a p q : Fin (Module.finrank ℝ E),
      Lv 0 0 1 0 KL M MA MB cl (L (bB (E := E) a) p q)) :
    ∀ a i j : Fin (Module.finrank ℝ E),
      Lv 0 0 1 2 (idxCard E * (idxCard E * ((KI * KI) * KL))) M MA MB cl (jdInv A L a i j) := by
  intro a i j
  refine Lv.neg ?_
  refine Lv.sum (fun p => ?_) hh ?_
  · refine Lv.sum (fun q => ?_) hh ?_
    · exact Lv.mul (Lv.mul (hInv i p) (hInv j q) hh hI hI) (hL a p q) hh
        (mul_nonneg hI hI) hK
    · positivity
  · positivity

/-- The derivative of the background Christoffel symbol, at level `(0,0,2,2)`. -/
lemma chain_jdGamU_bg {M MA MB cl KI KK KD KJ : ℝ} (hh : Hyp M MA MB cl)
    (hI : 0 ≤ KI) (hK : 0 ≤ KK) (hD : 0 ≤ KD) (hJ : 0 ≤ KJ)
    {A : MatE (E := E)} {L : LinMat E} {B : BilMat E}
    (hInv : ∀ r s : Fin (Module.finrank ℝ E), Lv 0 0 0 1 KI M MA MB cl (jInv A r s))
    (hKz : ∀ a b c : Fin (Module.finrank ℝ E), Lv 0 0 1 0 KK M MA MB cl (jKz L a b c))
    (hKzD : ∀ m a b c : Fin (Module.finrank ℝ E), Lv 0 0 1 0 KD M MA MB cl (jKzD B m a b c))
    (hjdInv : ∀ a i j : Fin (Module.finrank ℝ E),
      Lv 0 0 1 2 KJ M MA MB cl (jdInv A L a i j)) :
    ∀ a r i j : Fin (Module.finrank ℝ E),
      Lv 0 0 2 2 (idxCard E * ((KJ * KK) + (KI * KD))) M MA MB cl (jdGamU A L B a r i j) := by
  intro a r i j
  refine Lv.sum (fun p => ?_) hh ?_
  · exact Lv.add (Lv.mul (hjdInv a r p) (hKz i j p) hh hJ hK)
      (Lv.mono (Lv.mul (hInv r p) (hKzD a i j p) hh hI hD) hh (mul_nonneg hI hD)
        (by omega) (by omega) (by omega) (by omega))
      hh (mul_nonneg hJ hK) (mul_nonneg hI hD)
  · positivity

end

end Work.Diff.STE.Lead
