import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The per-term bound of the `A · D_z f` flat row

Leibniz expands `D_z^bD_θ^a(A·D_zf)` into the terms `C·(D_z^{j}D_θ^{i}A)·(D_z^{b-j+1}D_θ^{a-i}f)`.
This module bounds one such term against the `ℋ⁶`-integrand (plus the angular Hardy slot `HH`),
pricing the coefficient slot by the `𝒲^{6,∞}`-norm and the flat bounds on `∂_θA`.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

theorem rowDz_term_bound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K Kf : ℝ) (a b : ℕ) (q : ℝ) (HH : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K → 0 ≤ Kf →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      a + b ≤ 6 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
        canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ) →
      ∀ (i j : ℕ), i ≤ a → j ≤ b → 1 ≤ i + j → ∀ z θ : ℝ,
        0 < z → 0 < θ → θ < Real.pi / 2 →
        canonW q z θ * |Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ C * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) := by
  obtain ⟨C1f, hC1fpos, hflat⟩ := Work.FTS.TransportS.flat_mixed_le 1
  refine ⟨4000 * (1 + C1f) + 1, by positivity, ?_⟩
  intro α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hab hq0 hqγ hqη0
    hqcases hHH hHHnn i j hi hj hij z θ hz hθ hθ2
  have hα0 : 0 < α := hα.1
  have hKnn : 0 ≤ K :=
    le_trans (Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hAwl) hAK
  have hCBnn : 0 ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by positivity
  -- ## the pricing of the coefficient slots
  have hAz : ∀ (j : ℕ), j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j 0 A z θ| ≤ 1000 * K := by
    intro j hj z θ hz hθ hθ2
    have h := Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 hAsm hAwl hj hz ⟨hθ, hθ2⟩
    calc |Work.Spaces.mixed j 0 A z θ| = |Work.Spaces.DzIter j A z θ| := rfl
      _ ≤ 1000 * Work.Spaces.WlInf α 6 A := h
      _ ≤ 1000 * K := by linarith
  have hAm : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ|
        ≤ 1000 * K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro i j hi hij z θ hz hθ hθ2
    have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 hα0 hAsm hAwl hi hij hz
      ⟨hθ, hθ2⟩
    have hYnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      have h0 : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos ⟨hθ, hθ2⟩)
      exact mul_nonneg (by linarith) (Real.rpow_nonneg h0 _)
    calc |Work.Spaces.mixed j i A z θ|
        ≤ 1000 * (Work.Spaces.WlInf α 6 A
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := h
      _ ≤ 1000 * (K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAK hYnn) (by norm_num)
      _ = 1000 * K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
  have hAf : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ C1f * Real.sin (2 * θ) * Kf := by
    intro i j hi hij z θ hz hθ hθ2
    refine hflat A hAsm Kf hKfnn ?_ i j hi (by omega) z θ hz hθ hθ2
    intro b₁ i₁ hbi z' θ' hz' hθ' hθ''
    have hb : b₁ = 0 ∨ b₁ = 1 := by omega
    have hi' : i₁ = 0 ∨ i₁ = 1 := by omega
    rcases hb with rfl | rfl <;> rcases hi' with rfl | rfl
    · simpa using hKf0 z' θ' hz' hθ' hθ''
    · simpa using hKf2 z' θ' hz' hθ' hθ''
    · simpa using hKf1 z' θ' hz' hθ' hθ''
    · omega
  -- ## the slot domination of the datum's own slot
  have hZc : ∀ e : ℝ, e ≤ Work.Spaces.gam α → (a = 0 → e ≤ Work.Spaces.eta) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        canonW e z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro e he heη z θ hz hθ hθ2
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
    rcases Nat.eq_zero_or_pos a with ha0 | ha
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := e)
          (h := f) (heη rfl) hθI b (by omega)
    · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := e)
        (h := f) he hθI b a ha (by omega)
  -- ## the case analysis
  have hmain : canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ (4000 * (1 + C1f) * (1 + K + Kf))
        * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    by_cases hi0 : i = 0
    · -- ### Case A: `i = 0`
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
        subst hi0
        rw [Nat.sub_zero]
        rcases Nat.eq_zero_or_pos a with ha0 | ha
        · subst ha0
          simpa only [Work.Spaces.mixed_zero_right] using
            Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := q)
              (h := f) (hqη0 rfl) hθI (b - j + 1) (by omega)
        · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q)
            (h := f) hqγ hθI (b - j + 1) a ha (by omega)
      have hXb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ 1000 * K * canonW q z θ := by
        intro z θ hz hθ hθ2
        subst hi0
        have h := hAz j (by omega) z θ hz hθ hθ2
        have h2 : canonW q z θ * |Work.Spaces.mixed j 0 A z θ| ≤ canonW q z θ * (1000 * K) :=
          mul_le_mul_of_nonneg_left h (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
        linarith [h2]
      have hres := rowDz_term_le (α := α) (q := q) (e := q) (M := 1000 * K)
        (X := Work.Spaces.mixed j i A)
        (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
        (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
        (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
        (by positivity) hXb hYb (hZc q hqγ hqη0) z θ hz hθ hθ2
      refine le_trans hres ?_
      have hMle := rowDz_const1 hC1fpos hKnn hKfnn
      calc (1000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          = (2 * (1000 * K)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
        _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
        _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
    · -- ### Case B/C: `1 ≤ i`
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have ha0 : ¬ (a = 0) := by omega
      by_cases hle : i + j ≤ 2
      · -- ### Case B: the flat σ-gain
        have heη : q - 1 ≤ Work.Spaces.eta := by
          rcases hqcases with h | h | h
          · rw [h]; linarith [Work.Spaces.eta_pos]
          · rw [h]; rw [Work.Spaces.eta]; norm_num
          · rw [h, Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.2]
        have heγ : q - 1 ≤ Work.Spaces.gam α := by linarith [hqγ]
        have hYc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW (q - 1) z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
          intro z θ hz hθ hθ2
          have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
          rcases Nat.eq_zero_or_pos (a - i) with h0 | hpos
          · rw [h0, Work.Spaces.mixed_zero_right]
            exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α)
              (q := q - 1) (h := f) heη hθI (b - j + 1) (by omega)
          · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α)
              (q := q - 1) (h := f) heγ hθI (b - j + 1) (a - i) hpos (by omega)
        have hXs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ (C1f * Kf) * canonW (q - 1) z θ := by
          intro z θ hz hθ hθ2
          have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos ⟨hθ, hθ2⟩
          have h2 : canonW q z θ * (Real.sin (2 * θ)) = canonW (q - 1) z θ := by
            have h3 := rowDz_canonW_mul_sigma (q := q) (t := 1) (z := z) (θ := θ) hσp
            simpa using h3
          rw [← h2]
          calc canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (C1f * Real.sin (2 * θ) * Kf) :=
                mul_le_mul_of_nonneg_left (hAf i j hi1 hle z θ hz hθ hθ2)
                  (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
            _ = (C1f * Kf) * (canonW q z θ * Real.sin (2 * θ)) := by ring
        have hres := rowDz_term_le (α := α) (q := q) (e := q - 1) (M := C1f * Kf)
          (X := Work.Spaces.mixed j i A)
          (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
          (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
          (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
          (mul_nonneg hC1fpos.le hKfnn) hXs hYc
          (hZc (q - 1) heγ (fun h => absurd h ha0)) z θ hz hθ hθ2
        refine le_trans hres ?_
        have hMle := rowDz_const2 hC1fpos hKnn hKfnn
        calc (C1f * Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            = (2 * (C1f * Kf)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
          _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
          _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
      · -- ### Case C: `3 ≤ i + j`
        have heγ : q - α / 5 ≤ Work.Spaces.gam α := by linarith [hqγ]
        have hXs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ (2000 * K) * canonW (q - α / 5) z θ := by
          intro z θ hz hθ hθ2
          have hασ : α + Real.sin (2 * θ) ≤ 2 := by
            have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
            linarith [hα.2]
          have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos ⟨hθ, hθ2⟩
          have h2 : canonW q z θ * (Real.sin (2 * θ)) ^ (α / 5) = canonW (q - α / 5) z θ :=
            rowDz_canonW_mul_sigma (q := q) (t := α / 5) hσp
          have h1 : canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5))) :=
            mul_le_mul_of_nonneg_left (hAm i j hi1 (by omega) z θ hz hθ hθ2)
              (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
          have h3 : canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)))
              = 1000 * K * (α + Real.sin (2 * θ)) * canonW (q - α / 5) z θ := by
            rw [← h2]; ring
          have h5 : 0 ≤ 1000 * K * canonW (q - α / 5) z θ :=
            mul_nonneg (by positivity) (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
          have h6 : (1000 * K * canonW (q - α / 5) z θ) * (α + Real.sin (2 * θ))
              ≤ (1000 * K * canonW (q - α / 5) z θ) * 2 :=
            mul_le_mul_of_nonneg_left hασ h5
          calc canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5))) := h1
            _ = 1000 * K * (α + Real.sin (2 * θ)) * canonW (q - α / 5) z θ := h3
            _ = (1000 * K * canonW (q - α / 5) z θ) * (α + Real.sin (2 * θ)) := by ring
            _ ≤ (1000 * K * canonW (q - α / 5) z θ) * 2 := h6
            _ = (2000 * K) * canonW (q - α / 5) z θ := by ring
        rcases Nat.eq_zero_or_pos (a - i) with hai0 | haipos
        · -- the middle slot is pure
          rw [hai0, Work.Spaces.mixed_zero_right]
          have hYpure : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              canonW (q - α / 5) z θ * (Work.Spaces.DzIter (b - j + 1) f z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α 6 f z θ + HH z θ := by
            intro z θ hz hθ hθ2
            have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
            by_cases hqη : q ≤ Work.Spaces.eta
            · have he : q - α / 5 ≤ Work.Spaces.eta := by linarith
              exact le_trans
                (Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α)
                  (q := q - α / 5) (h := f) he hθI (b - j + 1) (by omega))
                (le_add_of_nonneg_right (hHHnn z θ hz hθ hθ2))
            · have hqg : q = Work.Spaces.gam α := by
                rcases hqcases with h | h | h
                · exact absurd (le_of_eq h) hqη
                · rw [h] at hqη; exact absurd (Work.Spaces.eta_pos.le) hqη
                · exact h
              have he : q - α / 5 = 1 - α / 10 := by rw [hqg]; rw [Work.Spaces.gam]; ring
              rw [he]
              have hmem : b - j + 1 ≤ 5 := by omega
              exact le_trans (hHH z θ hz hθ hθ2 (b - j + 1) hmem)
                (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 6 f z θ))
          have hres := rowDz_term_le (α := α) (q := q) (e := q - α / 5) (M := 2000 * K)
            (X := Work.Spaces.mixed j i A) (Y := Work.Spaces.DzIter (b - j + 1) f)
            (Z := Work.Spaces.mixed b a f)
            (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)
            (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (by positivity) hXs hYpure (hZc (q - α / 5) heγ (fun h => absurd h ha0))
            z θ hz hθ hθ2
          refine le_trans hres ?_
          have hMle := rowDz_const3 hC1fpos hKnn hKfnn
          have hsum : Work.Spaces.HkIntegrand α 6 f z θ + HH z θ
                + Work.Spaces.HkIntegrand α 6 f z θ
              ≤ 2 * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
            linarith [hHHnn z θ hz hθ hθ2, Work.Spaces.HkIntegrand_nonneg α 6 f z θ]
          calc (2000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ
                + Work.Spaces.HkIntegrand α 6 f z θ)
              ≤ (2000 * K) * (2 * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = (2 * (2000 * K)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by ring
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf))
                * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
                mul_le_mul_of_nonneg_right hMle
                  (by linarith [Work.Spaces.HkIntegrand_nonneg α 6 f z θ, hHHnn z θ hz hθ hθ2])
        · -- the middle slot is mixed
          have hYc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              canonW (q - α / 5) z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
            intro z θ hz hθ hθ2
            have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
            exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α)
              (q := q - α / 5) (h := f) heγ hθI (b - j + 1) (a - i) haipos (by omega)
          have hres := rowDz_term_le (α := α) (q := q) (e := q - α / 5) (M := 2000 * K)
            (X := Work.Spaces.mixed j i A)
            (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
            (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (by positivity) hXs hYc (hZc (q - α / 5) heγ (fun h => absurd h ha0))
            z θ hz hθ hθ2
          refine le_trans hres ?_
          have hMle := rowDz_const3 hC1fpos hKnn hKfnn
          calc (2000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
              = (2 * (2000 * K)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
                mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf))
                * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
                mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
  -- ## the constant
  refine le_trans hmain ?_
  have hX : 0 ≤ (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
    mul_nonneg (by linarith)
      (add_nonneg (hHHnn z θ hz hθ hθ2) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ))
  calc 4000 * (1 + C1f) * (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      = 4000 * (1 + C1f) * ((1 + K + Kf)
          * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by ring
    _ ≤ (4000 * (1 + C1f) + 1) * ((1 + K + Kf)
          * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
    _ = (4000 * (1 + C1f) + 1) * (1 + K + Kf)
          * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) := by ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
