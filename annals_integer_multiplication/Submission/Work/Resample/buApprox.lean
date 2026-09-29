import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.buPerm
import Submission.Work.Resample.buEroundW
import Submission.Work.Resample.buFixed
import Submission.Work.Resample.buErow
import Submission.Work.Resample.buWtAcc
import Submission.Work.Resample.buWdAcc
import Submission.Work.Resample.buDscW
import Submission.Work.Resample.buArith
import Submission.Work.Resample.buNeumannErr

/-!
# `Work.Resample.buApprox`

The *mathematical* content of `Work.Resample.sliceBu` for the computable map
`Φ = buPhi (buWt p α s t) (buWd p α s t)` (paper Prop. 4.7(ii), Lemmas 4.8–4.12).

`buPhiSpecZ` is the core estimate: given

* the accuracy `hwacc` of the computable Gaussian weights `buWt` (`Work.Resample.buWtAcc`),
* the accuracy `hdacc` of the computable diagonal weights `buWd` (`Work.Resample.buWdAcc`),
* the truncated-Neumann estimate `hNe` (`Work.Resample.buNeumannErr`),
* the diagonal-scaling estimate `hDsc` (`Work.Resample.buDscW`),
* the arithmetic bound `harith` (`Work.Resample.buArith`),

the map `P̃_sᵀ ∘ D̃' ∘ J̃' ∘ (C̃ P̃_t)` preserves the disc `C̃s◦` and approximates `resB s t α`
with error `< p²`.  The word-level facts (the existence of the uniform programs `prep`, `q`) are
`Work.Resample.buPrep` and `Work.Resample.buQW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- **The one-dimensional `B̃` estimate.**  Let `W : Fin t → ℂ` be the input vector,
`z : Fin s → ℤ × ℤ` the selected (and reduced) input, `v0` its halving, `Z = fxC p ∘ z`.
Then the computed vector `D̃' (J̃' v0)` (with the tabulated weights `buWd`, `buWt`) is in the disc
at the permuted index `egGam k` and is within `p²·2^{-p}` of `(resB s t α) ·ᵥ W`. -/
theorem buPhiSpecZ (p α s t : ℕ) (hs0 : 0 < s) (hst : s < t) (hcop : Nat.Coprime s t)
    (hwacc : ∀ (ℓ h : ℤ), h ∈ egHset (egM p α) →
      |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h| ≤ 4 / (2 : ℝ) ^ p)
    (hdacc : ∀ ℓ : Fin s, |(buWd p α s t (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
      - (HvdH.diagD' s t α ℓ ℓ).re| ≤ 2 / (2 : ℝ) ^ p)
    (hNe : ∀ (z : Fin s → ℤ × ℤ), (∀ ℓ, HvdH.inDisc p (z ℓ)) →
      (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (buJsum (buWt p α s t) p α s t hs0
            (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)
          - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec (fun ℓ => HvdH.fxC p (z ℓ)))) ℓ‖
        ≤ 1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24)) ∧
      (∀ ℓ, ‖HvdH.fxC p (buJsum (buWt p α s t) p α s t hs0
            (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)‖ ≤ 1))
    (hDsc : ∀ (Wd : ℤ → ℤ) (ε : ℝ), 0 ≤ ε → ε ≤ 2 →
      (∀ ℓ : Fin s, |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
        - (HvdH.diagD' s t α ℓ ℓ).re| ≤ ε / (2 : ℝ) ^ p) →
      ∀ (X : Fin s → ℤ × ℤ), (∀ ℓ, HvdH.inDisc p (X ℓ)) →
      ∀ (B : ℝ), (∀ ℓ, ‖HvdH.fxC p (X ℓ)‖ ≤ B) →
      ∀ (y : Fin s → ℂ) (e : ℝ), (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (X ℓ) - y ℓ‖ ≤ e) →
        (∀ ℓ, HvdH.inDisc p (buDsc Wd p s X ℓ)) ∧
        (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (buDsc Wd p s X ℓ)
          - (HvdH.diagD' s t α).mulVec y ℓ‖ ≤ 2 + e + ε * B))
    (harith : 5 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24) < (p : ℝ) ^ 2)
    (W : Fin t → ℂ) (z : Fin s → ℤ × ℤ) (v0 : Fin s → ℤ × ℤ)
    (hz : ∀ ℓ, HvdH.inDisc p (z ℓ))
    (hv0 : ∀ ℓ, v0 ℓ = (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2))
    (Z : Fin s → ℂ) (hZ : ∀ ℓ, Z ℓ = HvdH.fxC p (z ℓ))
    (hW : ∀ ℓ : Fin s, Z ℓ = HvdH.vget W (egNu s t (ℓ : ℕ))) :
    (∀ k : Fin s, HvdH.inDisc p (buDsc (buWd p α s t) p s
        (buJsum (buWt p α s t) p α s t hs0 v0) (egGam s t hs0 hcop.symm k))) ∧
    (∀ k : Fin s, ‖HvdH.fxC p (buDsc (buWd p α s t) p s
        (buJsum (buWt p α s t) p α s t hs0 v0) (egGam s t hs0 hcop.symm k))
        - (HvdH.resB s t α).mulVec W k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2) := by
  -- ### (A)  the truncated Neumann estimate, rewritten to `v0` and `Z`
  have hv0f : v0 = fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2) := funext hv0
  have hZf : (fun ℓ => HvdH.fxC p (z ℓ)) = Z := funext (fun ℓ => (hZ ℓ).symm)
  have hNe' := hNe z hz
  have hAcc : ∀ ℓ : Fin s, (2 : ℝ) ^ p * ‖HvdH.fxC p
        (buJsum (buWt p α s t) p α s t hs0 v0 ℓ)
      - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)) ℓ‖
      ≤ 1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24) := by
    intro ℓ
    have h := hNe'.1 ℓ
    rw [← hv0f, hZf] at h
    exact h
  have hNorm : ∀ ℓ : Fin s, ‖HvdH.fxC p (buJsum (buWt p α s t) p α s t hs0 v0 ℓ)‖ ≤ 1 := by
    intro ℓ
    have h := hNe'.2 ℓ
    rw [← hv0f] at h
    exact h
  -- ### (B)  the diagonal scaling
  have hD := hDsc (buWd p α s t) 2 (by norm_num) (by norm_num) hdacc
    (buJsum (buWt p α s t) p α s t hs0 v0)
    (fun ℓ => inDisc_of_norm_fxC_le_one p (hNorm ℓ))
    1 (fun ℓ => hNorm ℓ)
    ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z))
    (1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24))
    (fun ℓ => hAcc ℓ)
  -- ### (C)  the two permutations `C̃ P̃_t` and `P̃_sᵀ`
  have hW' : ∀ ℓ : Fin s, HvdH.vget W (egNu s t (ℓ : ℕ)) = Z ℓ := by
    intro ℓ
    have hlt : egNu s t (ℓ : ℕ) < t := by
      simp only [egNu, egSigT]
      exact Nat.mod_lt _ (by omega)
    have h := (hW ℓ).symm
    rw [show HvdH.vget W (egNu s t (ℓ : ℕ)) = W ⟨egNu s t (ℓ : ℕ), hlt⟩ from by
      simp [HvdH.vget, hlt]] at h ⊢
    exact h
  have hZrow : (HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec W) = Z := by
    funext ℓ
    rw [Matrix.mulVec_mulVec, (buPerm s t hs0 hst hcop.symm W Z ℓ ⟨0, hs0⟩).1]
    exact hW' ℓ
  have hresB : (HvdH.resB s t α).mulVec W
      = ((HvdH.permS s t).transpose).mulVec
        ((HvdH.diagD' s t α).mulVec ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z))) := by
    rw [HvdH.resB]
    simp only [← Matrix.mulVec_mulVec]
    rw [hZrow, Matrix.smul_mulVec]
  have hperm2 : ∀ k : Fin s, (((HvdH.permS s t).transpose).mulVec
        ((HvdH.diagD' s t α).mulVec ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)))) k
      = ((HvdH.diagD' s t α).mulVec ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z)))
          (egGam s t hs0 hcop.symm k) := by
    intro k
    exact (buPerm s t hs0 hst hcop.symm W
      ((HvdH.diagD' s t α).mulVec ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec Z))) ⟨0, hs0⟩ k).2
  -- ### (D)  conclusion
  constructor
  · intro k
    exact hD.1 (egGam s t hs0 hcop.symm k)
  · intro k
    have h2 : ‖HvdH.fxC p (buDsc (buWd p α s t) p s
          (buJsum (buWt p α s t) p α s t hs0 v0) (egGam s t hs0 hcop.symm k))
        - (HvdH.resB s t α).mulVec W k‖ * (2 : ℝ) ^ p
        ≤ 2 + (1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24)) + 2 * 1 := by
      have h1 := hD.2 (egGam s t hs0 hcop.symm k)
      rw [← hperm2 k, ← hresB] at h1
      conv_lhs => rw [mul_comm]
      exact h1
    exact lt_of_le_of_lt h2 (by linarith [harith])


/-- Unfolding `buPhi` at a single coordinate: the output is the `egGam k`-th entry of
`D̃' (J̃' v0)`, where `v0` is the halving of the input selected by `egNu`. -/
lemma buPhi_apply (Wt : ℤ → ℤ → ℤ) (Wd : ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s)
    (hcop : Nat.Coprime t s) (w : Fin t → ℤ × ℤ) (k : Fin s) :
    buPhi Wt Wd p α s t hs hcop w k
      = buDsc Wd p s (buJsum Wt p α s t hs
          (fun ℓ => (Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).1 2,
                     Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).2 2)))
        (egGam s t hs hcop k) := by
  have hlt : ((egGam s t hs hcop k : Fin s) : ℕ) < s := (egGam s t hs hcop k).isLt
  simp only [buPhi, egGet]
  rw [dif_pos hlt]

/-- The two mathematical conclusions of `sliceBu` for the computable map
`Φ = buPhi (buWt p α s t) (buWd p α s t)` (paper Prop. 4.7(ii)). -/
theorem buPhiSpec (RM : HvdH.ResMath1DProp) (p α s t : ℕ) (hs : 2 ≤ s) (hs0 : 0 < s)
    (hst : s < t) (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (htail : ∀ ℓ : Fin s,
      ∑' h : ℤ, (if egM p α < h.natAbs then |egW s t α (ℓ : ℤ) h| else 0)
        ≤ 3 / (2 : ℝ) ^ p) :
    (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
        HvdH.inDisc p (buPhi (buWt p α s t) (buWd p α s t) p α s t hs0 hcop.symm w k)) ∧
    (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
        ‖HvdH.fxC p (buPhi (buWt p α s t) (buWd p α s t) p α s t hs0 hcop.symm w k)
            - (HvdH.resB s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p
          < (p : ℝ) ^ 2) := by
  have hwacc : ∀ (ℓ h : ℤ), h ∈ egHset (egM p α) →
      |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h| ≤ 4 / (2 : ℝ) ^ p :=
    fun ℓ h hh => buWtAcc p α s t hs hst hα hp ℓ h (Finset.mem_erase.mp hh).1
  have hdacc : ∀ ℓ : Fin s, |(buWd p α s t (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
      - (HvdH.diagD' s t α ℓ ℓ).re| ≤ 2 / (2 : ℝ) ^ p :=
    fun ℓ => buWdAcc p α s t hs0 hα hp hαp ℓ
  have h78 : ∀ ℓ : Fin s, ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 7 / 8 :=
    fun ℓ => (buFixed p α s t hα (0, 0) (by simp [HvdH.inDisc]) ℓ).2
  have hrow : ∀ (ℓ : Fin s) (x : Fin s → ℂ), ((HvdH.Emat s t α).mulVec x) ℓ = ∑' h : ℤ,
      (if h = 0 then 0 else ((egW s t α (ℓ : ℤ) h : ℝ) : ℂ)
        * x (egIdx s hs0 ((ℓ : ℤ) + h))) :=
    fun ℓ x => buErow s t α hs0 hst (by omega) ℓ x
  have hNe : ∀ (z : Fin s → ℤ × ℤ), (∀ ℓ, HvdH.inDisc p (z ℓ)) →
      (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (buJsum (buWt p α s t) p α s t hs0
            (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)
          - ((1 / 2 : ℂ) • ((HvdH.Jmat s t α).mulVec (fun ℓ => HvdH.fxC p (z ℓ)))) ℓ‖
        ≤ 1 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24)) ∧
      (∀ ℓ, ‖HvdH.fxC p (buJsum (buWt p α s t) p α s t hs0
            (fun ℓ => (Int.tdiv (z ℓ).1 2, Int.tdiv (z ℓ).2 2)) ℓ)‖ ≤ 1) :=
    fun z hz => buNeumannErr RM p α s t hs hs0 hst hcop hα hp hαp hθ hwacc hrow htail z hz
  have hDsc : ∀ (Wd : ℤ → ℤ) (ε : ℝ), 0 ≤ ε → ε ≤ 2 →
      (∀ ℓ : Fin s, |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
        - (HvdH.diagD' s t α ℓ ℓ).re| ≤ ε / (2 : ℝ) ^ p) →
      ∀ (X : Fin s → ℤ × ℤ), (∀ ℓ, HvdH.inDisc p (X ℓ)) →
      ∀ (B : ℝ), (∀ ℓ, ‖HvdH.fxC p (X ℓ)‖ ≤ B) →
      ∀ (y : Fin s → ℂ) (e : ℝ), (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (X ℓ) - y ℓ‖ ≤ e) →
        (∀ ℓ, HvdH.inDisc p (buDsc Wd p s X ℓ)) ∧
        (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (buDsc Wd p s X ℓ)
          - (HvdH.diagD' s t α).mulVec y ℓ‖ ≤ 2 + e + ε * B) :=
    fun Wd ε h0 h2 hWd X hX B hB y e he =>
      buDscW RM p α s t hα hp h78 Wd ε h0 h2 hWd X hX B hB y e he
  have harith : 5 + (egN p α s t : ℝ) * (18 * (egM p α : ℝ) + 24) < (p : ℝ) ^ 2 :=
    buArith p α s t hs hst hα hp hαp hθ
  have key : ∀ (w : Fin t → ℤ × ℤ), (∀ j, HvdH.inDisc p (w j)) →
      ∀ k : Fin s, (buPhi (buWt p α s t) (buWd p α s t) p α s t hs0 hcop.symm w k
        = buDsc (buWd p α s t) p s
            (buJsum (buWt p α s t) p α s t hs0
              (fun ℓ => (Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).1 2,
                         Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).2 2)))
            (egGam s t hs0 hcop.symm k)) := by
    intro w hw k
    rw [buPhi_apply]
  have hz' : ∀ (w : Fin t → ℤ × ℤ), (∀ j, HvdH.inDisc p (w j)) →
      ∀ ℓ : Fin s, HvdH.inDisc p (egGet w (egNu s t (ℓ : ℕ))) := by
    intro w hw ℓ
    have hlt : egNu s t (ℓ : ℕ) < t := by
      simp only [egNu, egSigT]
      exact Nat.mod_lt _ (by omega)
    rw [show egGet w (egNu s t (ℓ : ℕ)) = w ⟨egNu s t (ℓ : ℕ), hlt⟩ from by simp [egGet, hlt]]
    exact hw _
  have hW'' : ∀ (w : Fin t → ℤ × ℤ), ∀ ℓ : Fin s, HvdH.fxC p (egGet w (egNu s t (ℓ : ℕ)))
      = HvdH.vget (fun j => HvdH.fxC p (w j)) (egNu s t (ℓ : ℕ)) := by
    intro w ℓ
    have hlt : egNu s t (ℓ : ℕ) < t := by
      simp only [egNu, egSigT]
      exact Nat.mod_lt _ (by omega)
    rw [show egGet w (egNu s t (ℓ : ℕ)) = w ⟨egNu s t (ℓ : ℕ), hlt⟩ from by simp [egGet, hlt]]
    rw [show HvdH.vget (fun j => HvdH.fxC p (w j)) (egNu s t (ℓ : ℕ))
        = HvdH.fxC p (w ⟨egNu s t (ℓ : ℕ), hlt⟩) from by simp [HvdH.vget, hlt]]
  constructor
  · intro w hw k
    have hspec := buPhiSpecZ p α s t hs0 hst hcop hwacc hdacc hNe hDsc harith
        (fun j => HvdH.fxC p (w j))
        (fun ℓ => egGet w (egNu s t (ℓ : ℕ)))
        (fun ℓ => (Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).1 2,
                   Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).2 2))
        (hz' w hw) (fun ℓ => rfl)
        (fun ℓ => HvdH.fxC p (egGet w (egNu s t (ℓ : ℕ)))) (fun ℓ => rfl) (hW'' w)
    rw [key w hw k]
    exact hspec.1 k
  · intro w hw k
    have hspec := buPhiSpecZ p α s t hs0 hst hcop hwacc hdacc hNe hDsc harith
        (fun j => HvdH.fxC p (w j))
        (fun ℓ => egGet w (egNu s t (ℓ : ℕ)))
        (fun ℓ => (Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).1 2,
                   Int.tdiv (egGet w (egNu s t (ℓ : ℕ))).2 2))
        (hz' w hw) (fun ℓ => rfl)
        (fun ℓ => HvdH.fxC p (egGet w (egNu s t (ℓ : ℕ)))) (fun ℓ => rfl) (hW'' w)
    rw [key w hw k]
    exact hspec.2 k

/-! ## Cost monotonicity for the two uniform words -/

/-- The cost shape `egCostShape` of the slice word is monotone in the cost constant. -/
theorem egCostShape_mono {Cm : ℕ → ℕ} (hC : Monotone Cm) {K K' p α t : ℕ} (h : K ≤ K') :
    egCostShape K p α t Cm ≤ egCostShape K' p α t Cm := by
  unfold egCostShape
  have h1 : Cm (K * p) ≤ Cm (K' * p) := hC (Nat.mul_le_mul_right p h)
  have h2 : K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1)
      ≤ K' * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K' * p) + p + 1) := by
    apply Nat.mul_le_mul _ (Nat.add_le_add_right (Nat.add_le_add_right h1 p) 1)
    apply Nat.mul_le_mul _ le_rfl
    apply Nat.mul_le_mul _ le_rfl
    apply Nat.mul_le_mul h le_rfl
  have h3 : K * (t + 1) * (p + 1) ^ 2 ≤ K' * (t + 1) * (p + 1) ^ 2 := by
    apply Nat.mul_le_mul _ le_rfl
    apply Nat.mul_le_mul h le_rfl
  exact add_le_add h2 h3

/-- The preparation-word budget `K(t+1)(p+1)^K` is monotone in `K`. -/
theorem prepCost_mono {K K' p t : ℕ} (h : K ≤ K') :
    K * (t + 1) * (p + 1) ^ K ≤ K' * (t + 1) * (p + 1) ^ K' := by
  apply Nat.mul_le_mul _ (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le p)) h)
  exact Nat.mul_le_mul h le_rfl

/-! ## The interface glue: from the two uniform words to `SliceSpecB` -/

/-- **Assembly of the one-dimensional `B̃` specification.**  Given

* a preparation word `prep` and a slice word `q` with their uniform `WordR` specifications
  (`Work.Resample.buPrep`, `Work.Resample.buQW`),
* the mathematical content `hb` of the computable map `Φ = buPhi (buWt p α s t) (buWd p α s t)`
  (`Work.Resample.buPhiSpec`),

produce the single pair `(prep, q)` with one uniform cost constant `K = max K₁ K₂` satisfying the
`SliceSpecB` statement of `Work.Resample.sliceBu`. -/
theorem buSliceGlue (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (FL : HvdH.FxLib) (RM : HvdH.ResMath1DProp) (prep : HvdH.Cmd) (K₁ : ℕ)
    (hprep : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K₁ * p < N →
      HvdH.WordR main prep
        (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
        (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
          out = buTabList p α s t (by omega) hcop.symm ++ rest)
        (fun _ => K₁ * (t + 1) * (p + 1) ^ K₁))
    (q : HvdH.Cmd) (K₂ : ℕ)
    (hq : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → K₂ * p < N →
      HvdH.WordR main q
        (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
          vs = HvdH.ofList (u.map HvdH.cfxVal) :: buTabList p α s t (by omega) hcop.symm ++ rest ∧
          u.length = t ∧ (∀ z ∈ u, HvdH.inDisc p z))
        (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
          vs = HvdH.ofList (u.map HvdH.cfxVal) :: buTabList p α s t (by omega) hcop.symm ++ rest ∧
          out = HvdH.cvecVal w :: buTabList p α s t (by omega) hcop.symm ++ rest ∧
          w.length = s ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
          (∀ k : Fin s, w.getD k (0, 0) = buPhi (buWt p α s t) (buWd p α s t) p α s t (by omega)
            hcop.symm (fun j => u.getD j (0, 0)) k))
        (fun _ => egCostShape K₂ p α t Cm))
    (hb : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hs0 : 0 < s) (hst : s < t) (hcop : Nat.Coprime s t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
      (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
          HvdH.inDisc p (buPhi (buWt p α s t) (buWd p α s t) p α s t hs0 hcop.symm w k)) ∧
      (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
          ‖HvdH.fxC p (buPhi (buWt p α s t) (buWd p α s t) p α s t hs0 hcop.symm w k)
              - (HvdH.resB s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < (p : ℝ) ^ 2)) :
    ∃ (prep' q' : HvdH.Cmd) (K : ℕ),
      ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
        (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
        (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1),
      ∃ (Φ : (Fin t → ℤ × ℤ) → (Fin s → ℤ × ℤ)) (P : List HvdH.Val),
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm →
            K * p < N →
          HvdH.WordR main prep'
            (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
            (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
              out = P ++ rest)
            (fun _ => K * (t + 1) * (p + 1) ^ K)) ∧
        (∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm →
            K * p < N →
          HvdH.WordR main q'
            (fun vs => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              u.length = t ∧ (∀ z ∈ u, HvdH.inDisc p z))
            (fun vs out => ∃ (u : List (ℤ × ℤ)) (rest : List HvdH.Val) (w : List (ℤ × ℤ)),
              vs = HvdH.ofList (u.map HvdH.cfxVal) :: P ++ rest ∧
              out = HvdH.cvecVal w :: P ++ rest ∧ w.length = s ∧ (∀ z ∈ w, HvdH.inDisc p z) ∧
              (∀ k : Fin s, w.getD k (0,0) = Φ (fun j => u.getD j (0,0)) k))
            (fun _ => K * (t + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (K * p) + p + 1) +
              K * (t + 1) * (p + 1) ^ 2)) ∧
        (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s, HvdH.inDisc p (Φ w k)) ∧
        (∀ w : Fin t → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin s,
          ‖HvdH.fxC p (Φ w k) - (HvdH.resB s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < (p : ℝ) ^ 2) := by
  refine ⟨prep, q, max K₁ K₂, ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ
  refine ⟨buPhi (buWt p α s t) (buWd p α s t) p α s t (by omega) hcop.symm,
    buTabList p α s t (by omega) hcop.symm, ?_, ?_, ?_, ?_⟩
  · intro main N Cm hmon hmb hN
    exact KL.conseq main prep _ _ _ _ _ _
      (hprep p α s t hs hst hcop htp hα hp hαp hθ main N Cm hmon hmb
        (lt_of_le_of_lt (Nat.mul_le_mul_right p (le_max_left K₁ K₂)) hN))
      (fun vs h => h) (fun vs out _ h => h)
      (fun vs _ => prepCost_mono (le_max_left K₁ K₂))
  · intro main N Cm hmon hmb hN
    exact KL.conseq main q _ _ _ _ _ _
      (hq p α s t hs hst hcop htp hα hp hαp hθ main N Cm hmon hmb
        (lt_of_le_of_lt (Nat.mul_le_mul_right p (le_max_right K₁ K₂)) hN))
      (fun vs h => h) (fun vs out _ h => h)
      (fun vs _ => egCostShape_mono hmon (le_max_right K₁ K₂))
  · intro w hw k
    exact (hb p α s t hs (by omega) hst hcop hα hp hαp hθ).1 w hw k
  · intro w hw k
    exact (hb p α s t hs (by omega) hst hcop hα hp hαp hθ).2 w hw k

end Work.Resample
