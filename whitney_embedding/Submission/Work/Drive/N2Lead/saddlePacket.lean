import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2.roundConfigPicture
import Submission.Work.Drive.N2Lead.exists_picture_of_curves
import Submission.Work.Drive.N2Lead.twistDefs

/-!
# The D2 saddle packet: the anchor picture `A` from a parametrised marked curve

`NOTES_LEAD_saddlePacket.md` §3.2 steps 2–3.  The anchor picture of the saddle window is built from
the component curves of the anchor level: the marked component (the one carrying the pin) is drawn
by a single prescribed `1`-periodic curve `C` (the polar curve `t ↦ cE3 (r (Θ t) * exp (i Θ t))`, or
its image under the Möbius slab twist `twistY a' 1`), and every other component is drawn as a round
circle far away at the parking spot `farPos j = (-20, 20 + 5 j, 1)`.

This file provides

* `farPos`, `farConfig`, `farCurve` — the parked round circles and their rows (smoothness,
  `1`-periodicity, injectivity modulo one period, nonvanishing velocity, and the norm gap
  `‖farCurve j t‖ ≥ 19`);
* `packetCurves` — the family of level curves (the marked curve plus the parked circles) with the
  four rows consumed by `Work.Drive.N2Lead.exists_picture_of_curves`;
* `packetPicture` — the resulting anchor picture `A : M → ℝ³` and its rows.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The round picture `t ↦ (cos t, sin t, 0)` lies on the unit circle. -/
lemma norm_roundPic (t : ℝ) : ‖Work.Drive.N2.roundPic t‖ = 1 := by
  have h2 : ‖Work.Drive.N2.roundPic t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Work.Drive.N2.roundPic, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ring_nf
    rw [Real.cos_sq_add_sin_sq]
    norm_num
  nlinarith [norm_nonneg (Work.Drive.N2.roundPic t)]

/-- The parking spot of the `j`-th idle circle. -/
def farPos (n : ℕ) (j : Fin n) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(-20 : ℝ), 20 + 5 * (j : ℕ), 1]

lemma farPos_apply (n : ℕ) (j : Fin n) :
    (farPos n j).ofLp = ![(-20 : ℝ), 20 + 5 * (j : ℕ), 1] := by
  simp [farPos]

lemma farPos_norm (n : ℕ) (j : Fin n) : 20 ≤ ‖farPos n j‖ := by
  have h := PiLp.norm_apply_le (farPos n j) (0 : Fin 3)
  have h0 : (farPos n j).ofLp 0 = (-20 : ℝ) := by rw [farPos_apply]; rfl
  rw [h0] at h
  simpa using h

lemma farPos_dist {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    5 ≤ ‖farPos n j - farPos n k‖ := by
  have hjk : ((j : ℕ) : ℝ) ≠ ((k : ℕ) : ℝ) := by
    have : (j : ℕ) ≠ (k : ℕ) := fun hc => h (Fin.ext hc)
    exact_mod_cast this
  have h := PiLp.norm_apply_le (farPos n j - farPos n k) (1 : Fin 3)
  have h1 : (farPos n j - farPos n k).ofLp 1
      = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
    simp only [PiLp.sub_apply, WithLp.ofLp_sub, farPos_apply]
    norm_num
    ring
  rw [h1] at h
  have habs : (1 : ℝ) ≤ |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| := by
    have hne : (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) ≠ 0 := sub_ne_zero.mpr hjk
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) = (m : ℝ) :=
      ⟨((j : ℕ) : ℤ) - ((k : ℕ) : ℤ), by push_cast; ring⟩
    rw [hm]
    have hm0 : m ≠ 0 := by
      intro h0
      exact hne (by rw [hm, h0]; norm_num)
    have := Int.one_le_abs hm0
    exact_mod_cast this
  have h2 : 5 * (1 : ℝ) ≤ 5 * |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| :=
    mul_le_mul_of_nonneg_left habs (by norm_num)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)] at h
  linarith

/-- The far round configuration: radius `1` about `farPos n j`, with zero phase. -/
def farConfig (n : ℕ) : Work.Drive.N2.RoundConfig n where
  pos := farPos n
  rad := fun _ => 1
  hrad := fun _ => one_pos
  phase := fun _ => 0

lemma farConfig_circle (n : ℕ) (j : Fin n) (t : ℝ) :
    (farConfig n).circle j t = farPos n j + Work.Drive.N2.ang t := by
  simp [Work.Drive.N2.RoundConfig.circle, farConfig, Work.Drive.N2.ang]

/-- The parked round circle at the `j`-th parking spot. -/
def farCurve (n : ℕ) (j : Fin n) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (farConfig n).circle j t

lemma farCurve_eq (n : ℕ) (j : Fin n) (t : ℝ) :
    farCurve n j t = farPos n j + Work.Drive.N2.ang t := farConfig_circle n j t

lemma farCurve_contDiff (n : ℕ) (j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (farCurve n j) := by
  have h : farCurve n j = fun t : ℝ => farPos n j + Work.Drive.N2.ang t :=
    funext (farCurve_eq n j)
  rw [h]
  exact ContDiff.add contDiff_const Work.Drive.N2.ang_contDiff

lemma norm_ang (t : ℝ) : ‖Work.Drive.N2.ang t‖ = 1 := by
  rw [Work.Drive.N2.ang, norm_roundPic]

lemma farCurve_norm (n : ℕ) (j : Fin n) (t : ℝ) : 19 ≤ ‖farCurve n j t‖ := by
  have h1 : ‖farPos n j‖ - ‖Work.Drive.N2.ang t‖ ≤ ‖farCurve n j t‖ := by
    have h := norm_sub_le (farPos n j + Work.Drive.N2.ang t) (Work.Drive.N2.ang t)
    rw [add_sub_cancel_right] at h
    rw [farCurve_eq]
    linarith
  linarith [farPos_norm n j, norm_ang t]

lemma farCurve_period (n : ℕ) (j : Fin n) (t : ℝ) : farCurve n j (t + 1) = farCurve n j t := by
  rw [farCurve_eq, farCurve_eq, Work.Drive.N2.ang_periodic]

lemma deriv_farCurve_ne_zero (n : ℕ) (j : Fin n) (t : ℝ) :
    deriv (farCurve n j) t ≠ 0 := by
  have hf := Work.Drive.N2.hasFDerivAt_circle (farConfig n) j t
  have hderiv : deriv (fun s : ℝ => (farConfig n).circle j s) t
      = (fderiv ℝ (fun s : ℝ => (farConfig n).circle j s) t) 1 := by
    rw [hf.fderiv]
    exact hf.hasDerivAt.deriv
  intro h0
  refine Work.Drive.N2.circle_deriv_ne_zero (farConfig n) j t ?_
  rw [← hderiv]
  exact h0

lemma farCurve_inj_self {n : ℕ} {j : Fin n} {s t : ℝ} (h : farCurve n j s = farCurve n j t) :
    ∃ m : ℤ, s = t + m := by
  have h' : (farConfig n).circle j s = (farConfig n).circle j t := h
  obtain ⟨k, hk⟩ := Work.Drive.N2.circle_eq_mod_one (farConfig n) j h'
  exact ⟨k, by linarith⟩

lemma farCurve_inj {n : ℕ} {j k : Fin n} {s t : ℝ} (h : farCurve n j s = farCurve n k t) :
    j = k ∧ ∃ m : ℤ, s = t + m := by
  by_cases hjk : j = k
  · subst hjk
    exact ⟨rfl, farCurve_inj_self h⟩
  · exfalso
    have h1 : ‖farPos n j - farPos n k‖ ≤ 2 := by
      have hsub : farPos n j - farPos n k
          = Work.Drive.N2.ang t - Work.Drive.N2.ang s := by
        have h' : farPos n j + Work.Drive.N2.ang s = farPos n k + Work.Drive.N2.ang t := by
          rw [← farCurve_eq, ← farCurve_eq]
          exact h
        calc farPos n j - farPos n k
            = (Work.Drive.N2.ang t - Work.Drive.N2.ang s)
              + ((farPos n j + Work.Drive.N2.ang s)
                - (farPos n k + Work.Drive.N2.ang t)) := by abel
          _ = Work.Drive.N2.ang t - Work.Drive.N2.ang s := by rw [h', sub_self, add_zero]
      rw [hsub]
      calc ‖Work.Drive.N2.ang t - Work.Drive.N2.ang s‖
          ≤ ‖Work.Drive.N2.ang t‖ + ‖Work.Drive.N2.ang s‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_ang, norm_ang]
        _ = 2 := by norm_num
    linarith [farPos_dist hjk, h1]

/-- The marked curve and a far circle are disjoint, by the norm gap. -/
lemma marked_far_ne {n : ℕ} {j : Fin n} {C : ℝ → EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hCnorm : ∀ t : ℝ, ‖C t‖ ≤ R) (hR : R < 19) (s t : ℝ) : C s ≠ farCurve n j t := by
  intro h
  have h1 : ‖farCurve n j t‖ ≤ R := by rw [← h]; exact hCnorm s
  linarith [farCurve_norm n j t, h1, hR]

/-- **The packet's family of level curves**: the marked component is drawn by `C`, the other
components by the parked round circles `farCurve`. -/
theorem packetCurves {n : ℕ} (i : Fin n) {C : ℝ → EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hCsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) (hCper : ∀ t : ℝ, C (t + 1) = C t)
    (hCinj : ∀ s t : ℝ, C s = C t → ∃ m : ℤ, s = t + m)
    (hCder : ∀ t : ℝ, deriv C t ≠ 0) (hCnorm : ∀ t : ℝ, ‖C t‖ ≤ R) (hR : R < 19) :
    ∃ c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c j)) ∧
      (∀ (j : Fin n) (t : ℝ), c j (t + 1) = c j t) ∧
      (∀ (j k : Fin n) (s t : ℝ), c j s = c k t → j = k ∧ ∃ m : ℤ, s = t + m) ∧
      (∀ (j : Fin n) (t : ℝ), deriv (c j) t ≠ 0) ∧ (∀ t : ℝ, c i t = C t) := by
  refine ⟨fun j => if j = i then C else farCurve n j, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · simpa [if_pos hj] using hCsm
    · simpa [if_neg hj] using farCurve_contDiff n j
  · intro j t
    by_cases hj : j = i
    · simpa [if_pos hj] using hCper t
    · simpa [if_neg hj] using farCurve_period n j t
  · intro j k s t hst
    change (if j = i then C else farCurve n j) s = (if k = i then C else farCurve n k) t at hst
    by_cases hj : j = i
    · rw [if_pos hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact ⟨hj.trans hk.symm, hCinj s t hst⟩
      · rw [if_neg hk] at hst
        exact absurd hst (marked_far_ne hCnorm hR s t)
    · rw [if_neg hj] at hst
      by_cases hk : k = i
      · rw [if_pos hk] at hst
        exact absurd hst.symm (marked_far_ne hCnorm hR t s)
      · rw [if_neg hk] at hst
        exact farCurve_inj hst
  · intro j t
    change deriv (fun s : ℝ => (if j = i then C else farCurve n j) s) t ≠ 0
    by_cases hj : j = i
    · rw [if_pos hj]
      simpa using hCder t
    · rw [if_neg hj]
      exact deriv_farCurve_ne_zero n j t
  · intro t
    show (if i = i then C else farCurve n i) t = C t
    rw [if_pos rfl]

/-- **The anchor picture from the family of curves.**  This is
`Work.Drive.N2Lead.exists_picture_of_curves` with its "`x` lies on the level" hypothesis
`∃ j t, x = L.γ j t` replaced by the equivalent value condition `f x = a` (through the `cover` row
of the `LevelCurves` datum), i.e. exactly the shape of the `hAsm`/`hAinj`/`hAimm` rows of
`Work.Drive.N2Lead.saddleWindow_of_packet_band_off`. -/
theorem packetPicture {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {a : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f a n)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x)
    {c : Fin n → ℝ → EuclideanSpace ℝ (Fin 3)}
    (hc : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c j))
    (hcper : ∀ (j : Fin n) (t : ℝ), c j (t + 1) = c j t)
    (hcinj : ∀ (j k : Fin n) (s t : ℝ), c j s = c k t → j = k ∧ ∃ m : ℤ, s = t + m)
    (hcderiv : ∀ (j : Fin n) (t : ℝ), deriv (c j) t ≠ 0) :
    ∃ A : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      (∀ (j : Fin n) (t : ℝ), A (L.γ j t) = c j t) ∧
      (∀ x y : M, f x = a → f y = a → A x = A y → x = y) ∧
      (∀ x : M, f x = a → ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
        mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0) := by
  obtain ⟨A, hsm, hcurve, hinj, himm⟩ :=
    Work.Drive.N2Lead.exists_picture_of_curves (f := f) (b := a) (n := n) L.γ hf hreg
      L.sm L.val L.per L.injIco L.cover L.disj L.ker c hc hcper hcinj hcderiv
  refine ⟨A, hsm, hcurve, ?_, ?_⟩
  · intro x y hx hy hxy
    exact hinj x y (L.cover x hx) (L.cover y hy) hxy
  · intro x hx v hvf hvA
    exact himm x (L.cover x hx) v hvf hvA


end

end Work.Drive.N2Lead
