/-
`DensNPointwise` — the pointwise bound
`K θ * |N α (F_* + W) Φg s θ| ≤ C (1+C₀)(1+B) (Maj s + s/(1+s)²) cos θ` on `Iθ`,
where `W = slice (JfamP ρ ε g) τ`, `Φg = slice (PsiCan Φs E (JfamP ρ ε g)) τ`.

The slots of `PhiTil α (F_* + W) Φg` (which is what `N` is built from) are compared with those of
`PhiTil α W Φg` (which is what `EpsDecay` bounds) by `Psivar0_slots_sub` + the locality lemmas
`Rop_congr_Q0`/`Uop_congr_Q0`/`Vop_congr_Q0` (the same route as `PTgadgets.pt_Xi_slots`, but
with the bounded-block `EpsDecay` (2026-10-12) the gain is the constant `13`).  The `Uop`-slot carries
the `sin 2θ` that pairs with `pth F`, so no `1/sin 2θ` is ever lost, and all the slots of `F` are
bounded by `(CFs+1)Q` with `Q = Maj s + s/(1+s)²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.StrongEps.E5Aux2.Helpers
import Submission.Work.FTS.StrongEps.E5Aux2.AngFacts
import Submission.Work.FTS.StrongEps.E5Aux2.AngIntK
import Submission.Work.FTS.StrongEps.E5Aux2.FstarSlotBounds
import Submission.Work.FTS.StrongEps.E5Aux2.ThetaDiff
import Submission.Work.FTS.StrongEps.E5Aux2.Psivar0_slots_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem DensNPointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  obtain ⟨CFs, hCFspos, hCFs⟩ := FstarSlotBounds
  have hCFs0 : 0 ≤ CFs := hCFspos.le
  refine ⟨200 * (CFs + 1) ^ 2 + 400, ?_, ?_⟩
  · nlinarith only [hCFspos]
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs θ hθ
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hs0 : (0 : ℝ) < s := hs
  obtain ⟨hMaj0, hMaj1, -, hSlot1, hBlk⟩ := hDec
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith only [hX, hXn, pow_pos hα0 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  -- ## the names
  set W : ℝ → ℝ → ℝ := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hWdef
  set Φg : ℝ → ℝ → ℝ :=
    slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ with hΦgdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hFdec : F = fun z θ => Work.Construction.Fstar α z θ + W z θ := by
    rw [hFdef, hWdef]; funext z θ; rfl
  set Ψ₀ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α W Φg with hΨ₀def
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α F Φg with hΨdef
  set H : ℝ := s / (1 + s) ^ 2 with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + H with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact add_nonneg (hMaj0 s) hH0
  have hMQ : Maj s ≤ Q := by rw [hQdef]; linarith only [hH0]
  have hHQ : H ≤ Q := by rw [hQdef]; linarith only [hMaj0 s]
  have hQfac : 0 ≤ (CFs + 1) * Q := mul_nonneg (by linarith) hQ0
  have hQ2 : Q ≤ 2 := by
    have h1 : Maj s ≤ 1 := hMaj1 s
    have h2 : H ≤ 1 := by
      rw [hHdef]
      rw [div_le_one (by positivity)]
      nlinarith
    rw [hQdef]; linarith
  -- ## the slot bounds of the interface (as functions of `Maj`)
  have hSlotR : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Rop α Ψ₀ z θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).1
  have hSlotU : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Uop α Ψ₀ z θ / Work.Construction.s2 θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).2.1
  have hSlotV : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Construction.Vop Ψ₀ z θ| ≤ 3 := by
    intro z hz θ hθ
    exact (hBlk z θ hz hθ).2.2
  -- ## the same slots for `PhiTil α (F_* + W) Φg` (with the `+10` of `Psivar0_slots_sub`)
  have hΘ : ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α W z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = -Real.sin (2 * θ) / (2 * (1 + z)) :=
    fun z θ hz => ThetaDiff hα0 hα1 hClass z θ hz
  have hΞid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z θ
        = Work.Construction.PhiTil α W Φg z θ - Real.sin (2 * θ) / (2 * (1 + z)) := by
    intro z θ hz h1 h2
    have h := hΘ z θ hz
    simp only [Work.Construction.PhiTil] at h ⊢
    ring_nf at h ⊢
    linarith
  have hlocR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α Ψ z θ
        = Work.Construction.Rop α
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  have hlocU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α Ψ z θ
        = Work.Construction.Uop α
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  have hlocV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop Ψ z θ
        = Work.Construction.Vop
            (fun z θ => Ψ₀ z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ := by
    intro z θ hz h1 h2
    rw [hΨdef, hΨ₀def, hFdec]
    exact Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0
      (fun z θ hz' h1' h2' => hΞid z θ hz' h1' h2') z θ hz h1 h2
  -- ## the F-slot bounds
  have hFstar : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Construction.Fstar α s θ'| ≤ CFs * H := by
    intro θ' hθ'
    have h := (hCFs (α := α) (z := s) (θ := θ') hαIoc hs0 hθ').1
    rw [hHdef]; exact h
  have hWval : ∀ θ', |W s θ'| ≤ Maj s := by
    intro θ'
    have h := hSlot1 s hs θ' 0 0 (by norm_num)
    simpa using h
  have hFval : ∀ θ' ∈ Work.Spaces.Iθ, |F s θ'| ≤ (CFs + 1) * Q := by
    intro θ' hθ'
    have h1 : |F s θ'| ≤ CFs * H + Maj s := by
      rw [hFdec]
      have h2 := abs_add_le (Work.Construction.Fstar α s θ') (W s θ')
      linarith only [h2, hFstar θ' hθ', hWval θ']
    have h3 : CFs * H + Maj s ≤ (CFs + 1) * Q := by
      have ha : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
      have hb : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
      have hc : (CFs + 1) * Q = CFs * Q + Q := by ring
      linarith only [ha, hb, hc]
    linarith only [h1, h3]
  -- ## the endpoint cases
  rcases eq_or_lt_of_le hθ.1 with hθz | hθz
  · subst hθz
    have hKz : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
    rw [hKz, zero_mul, Real.cos_zero, mul_one]
    have hCpos : 0 < 200 * (CFs + 1) ^ 2 + 400 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos.le (by linarith)) (by linarith)) hQ0
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · subst hθp
      have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hKp, zero_mul, Real.cos_pi_div_two, mul_zero]
    · -- ## the interior
      have hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθz, hθp⟩
      have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
      have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
      have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
      have hs2pos : 0 < Work.Construction.s2 θ := by
        rw [Work.Construction.s2]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith only [hθi.1]) (by linarith only [hθi.2])
      have hΞR : |Work.Construction.Rop α Ψ s θ| ≤ 13 := by
        rw [hlocR s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).1
        have h2 := hSlotR s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hΞU : |Work.Construction.Uop α Ψ s θ / Work.Construction.s2 θ| ≤ 13 := by
        rw [hlocU s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).2.1
        have h2 := hSlotU s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hΞV : |Work.Construction.Vop Ψ s θ| ≤ 13 := by
        rw [hlocV s θ hs0 hθi.1 hθi.2]
        have h := (Psivar0_slots_sub hαIoc hs0 hθi (Ψ1 := Ψ₀)).2.2
        have h2 := hSlotV s hs0 θ hθi
        rw [hΨ₀def] at h2
        linarith only [h, h2]
      have hUopLe : |Work.Construction.Uop α Ψ s θ| ≤ (13 : ℝ) * Work.Construction.s2 θ := by
        rw [abs_div, abs_of_pos hs2pos] at hΞU
        rw [div_le_iff₀ hs2pos] at hΞU
        linarith only [hΞU]
      -- ## the remaining `F`-slots
      have hFS : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
        Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
      have hpth_add : Work.Spaces.pth F s θ
          = Work.Spaces.pth (Work.Construction.Fstar α) s θ + Work.Spaces.pth W s θ := by
        have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
            F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
          intro z' θ' _ _ _; rw [hFdec]
        rw [Work.FTS.PhiStar.CoreAux.pth_congr_Q0 hpt s θ hs0 hθi.1 hθi.2]
        exact Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hFS hClass.reg s θ hs0 hθi.1 hθi.2
      have hpz_add : Work.Spaces.pz F s θ
          = Work.Spaces.pz (Work.Construction.Fstar α) s θ + Work.Spaces.pz W s θ := by
        have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
            F z' θ' = Work.Construction.Fstar α z' θ' + W z' θ' := by
          intro z' θ' _ _ _; rw [hFdec]
        rw [Work.FTS.GalFields.RHS.Sharp.pz_congr_Q0 hpt s θ hs0 hθi.1 hθi.2]
        exact Work.FTS.GalFields.RHS.Sharp.pz_add_Q0 hFS hClass.reg s θ hs0 hθi.1 hθi.2
      have hFstarDz : |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| ≤ CFs * H := by
        have h := (hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ).2.2.1
        rw [hHdef]; exact h
      have hFstarDth : |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ|
          ≤ CFs * H := by
        have h := (hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ).2.1
        rw [hHdef]; simpa only [Work.Construction.s2] using h
      have hWDz : |Work.Spaces.Dz W s θ| ≤ Maj s := by
        have h := hSlot1 s hs θ 1 0 (by norm_num); simpa using h
      have hWDth : |Work.Construction.s2 θ * Work.Spaces.pth W s θ| ≤ Maj s := by
        have h := hSlot1 s hs θ 0 1 (by norm_num)
        simpa [Work.Construction.s2, Work.Spaces.Dth] using h
      have hQadd : CFs * H + Maj s ≤ (CFs + 1) * Q := by
        have ha : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
        have hb : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
        have hc : (CFs + 1) * Q = CFs * Q + Q := by ring
        linarith only [ha, hb, hc]
      have hDzF : |Work.Spaces.Dz F s θ| ≤ (CFs + 1) * Q := by
        have h2' : Work.Spaces.Dz F s θ
            = Work.Spaces.Dz (Work.Construction.Fstar α) s θ + Work.Spaces.Dz W s θ := by
          rw [Work.Spaces.Dz, hpz_add, Work.Spaces.Dz, Work.Spaces.Dz]; ring
        rw [h2']
        have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
          (Work.Spaces.Dz W s θ)
        linarith only [h1, hFstarDz, hWDz, hQadd]
      have hs2pthF : |Work.Construction.s2 θ * Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
        have hdist : Work.Construction.s2 θ
            * (Work.Spaces.pth (Work.Construction.Fstar α) s θ + Work.Spaces.pth W s θ)
            = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Work.Construction.s2 θ * Work.Spaces.pth W s θ := by ring
        rw [hpth_add, hdist]
        have h1 := abs_add_le
          (Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) s θ)
          (Work.Construction.s2 θ * Work.Spaces.pth W s θ)
        linarith only [h1, hFstarDth, hWDth, hQadd]
      -- ## the angular moment of `F`
      have hFKF : |Work.Construction.FK F s| ≤ (CFs + 1) * Q := by
        have hFKdef : Work.Construction.FK F s
            = ∫ θ' in Work.Spaces.Iθ, F s θ' * Work.Spaces.K θ' := rfl
        have hK3 : ∀ θ' ∈ Work.Spaces.Iθ, Work.Spaces.K θ' ≤ 3 := by
          intro θ' hθ'
          have hs1 : Real.sin θ' ≤ 1 := Real.sin_le_one θ'
          have hs0' : 0 ≤ Real.sin θ' :=
            Real.sin_nonneg_of_mem_Icc ⟨hθ'.1, by linarith only [hθ'.2, Real.pi_pos]⟩
          have hc2 : Real.cos θ' ^ 2 ≤ 1 := by
            nlinarith only [Real.neg_one_le_cos θ', Real.cos_le_one θ', sq_nonneg (Real.cos θ')]
          rw [Work.Spaces.K]
          nlinarith
        have hmaj : ∀ θ' ∈ Work.Spaces.Iθ,
            |F s θ' * Work.Spaces.K θ'| ≤ ((CFs + 1) * Q) * Work.Spaces.K θ' := by
          intro θ' hθ'
          rw [abs_mul, abs_of_nonneg (hKnn θ' hθ')]
          exact mul_le_mul_of_nonneg_right (hFval θ' hθ') (hKnn θ' hθ')
        have hInt : Integrable ((fun θ' : ℝ => ((CFs + 1) * Q) * Work.Spaces.K θ'))
            (volume.restrict Work.Spaces.Iθ) :=
          (continuous_K.const_mul ((CFs + 1) * Q)).continuousOn.integrableOn_compact
            isCompact_Icc
        calc |Work.Construction.FK F s|
            ≤ ∫ θ' in Work.Spaces.Iθ, |F s θ' * Work.Spaces.K θ'| := by
              rw [hFKdef]
              simpa only [Real.norm_eq_abs] using
                (MeasureTheory.norm_integral_le_integral_norm
                  (μ := volume.restrict Work.Spaces.Iθ)
                  (f := fun θ' => F s θ' * Work.Spaces.K θ'))
          _ ≤ ∫ θ' in Work.Spaces.Iθ, ((CFs + 1) * Q) * Work.Spaces.K θ' :=
              MeasureTheory.setIntegral_mono_of_nonneg (fun θ' _ => abs_nonneg _) hmaj hInt
          _ = ((CFs + 1) * Q) * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.K θ') := by
              rw [MeasureTheory.integral_const_mul]
          _ = (CFs + 1) * Q := by rw [AngIntK, mul_one]
      -- ## the five summands of `N`
      have h11 : (13 : ℝ) ≤ 13 := le_rfl
      have hU1 : |2 * Work.Construction.Rop α Ψ s θ * F s θ| ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have h1 : |Work.Construction.Rop α Ψ s θ| ≤ 13 := le_trans hΞR h11
        calc 2 * |Work.Construction.Rop α Ψ s θ| * |F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) (hFval θ hθ)
                (abs_nonneg _) (by norm_num)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hU2 : |2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ|
          ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have h1 : 2 * |Work.Construction.Uop α Ψ s θ|
            ≤ 2 * ((13 : ℝ) * Work.Construction.s2 θ) :=
          mul_le_mul_of_nonneg_left hUopLe (by norm_num)
        have h2 : Work.Construction.s2 θ * |Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
          simpa only [abs_mul, abs_of_pos hs2pos] using hs2pthF
        have h3 : 2 * |Work.Construction.Uop α Ψ s θ| * |Work.Spaces.pth F s θ|
            ≤ 2 * ((13 : ℝ) * Work.Construction.s2 θ) * |Work.Spaces.pth F s θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUopLe (by norm_num)) (abs_nonneg _)
        have h4 : 2 * ((13 : ℝ) * Work.Construction.s2 θ) * |Work.Spaces.pth F s θ|
            = 2 * (13 : ℝ) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|) := by ring
        have h5 : 2 * (13 : ℝ) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
          mul_le_mul (by linarith only [h11] : 2 * (13 : ℝ) ≤ 2 * 13) h2
            (mul_nonneg hs2pos.le (abs_nonneg _)) (by norm_num)
        calc 2 * |Work.Construction.Uop α Ψ s θ| * |Work.Spaces.pth F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) := le_trans h3 (le_trans (le_of_eq h4) h5)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hU3 : |2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ|
          ≤ 26 * ((CFs + 1) * Q) := by
        rw [abs_mul, abs_mul]
        have h1 : |2 * α| ≤ 2 := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hα0]
          linarith
        have h2 : |Work.Construction.Vop Ψ s θ| ≤ 13 := le_trans hΞV h11
        calc |2 * α| * |Work.Construction.Vop Ψ s θ| * |Work.Spaces.Dz F s θ|
            ≤ 2 * 13 * ((CFs + 1) * Q) :=
              mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) hDzF
                (abs_nonneg _) (by norm_num)
          _ = 26 * ((CFs + 1) * Q) := by ring
      have hQQ : Q * Q ≤ 2 * Q := by
        have h := mul_le_mul_of_nonneg_left hQ2 hQ0
        exact le_trans h (le_of_eq (by ring))
      have hU4 : |(1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
          * Work.Spaces.pth F s θ| ≤ (CFs + 1) ^ 2 * Q := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), abs_of_pos hs2pos]
        have h2 : Work.Construction.s2 θ * |Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
          simpa only [abs_mul, abs_of_pos hs2pos] using hs2pthF
        have h3 : (1/2) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
              * |Work.Construction.FK F s|
            ≤ (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) hFKF (abs_nonneg _)
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hQfac)
        have h4 : (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q) ≤ (CFs + 1) ^ 2 * Q := by
          have hnn : 0 ≤ (CFs + 1) ^ 2 := by positivity
          have h5 : (1/2) * ((CFs + 1) * Q) * ((CFs + 1) * Q)
              = (1/2) * ((CFs + 1) ^ 2 * (Q * Q)) := by ring
          have h6 : (1/2) * ((CFs + 1) ^ 2 * (Q * Q)) ≤ (CFs + 1) ^ 2 * Q := by
            nlinarith only [hnn, hQ0, hQQ]
          rw [h5]; exact h6
        have h7 : ((1/2) * Work.Construction.s2 θ) * |Work.Construction.FK F s|
              * |Work.Spaces.pth F s θ|
            = (1/2) * (Work.Construction.s2 θ * |Work.Spaces.pth F s θ|)
              * |Work.Construction.FK F s| := by ring
        rw [h7]
        exact le_trans h3 h4
      have hU5 : |(Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ|
          ≤ 2 * (CFs + 1) ^ 2 * Q := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        have hs0' : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith only [hθ.2, Real.pi_pos]⟩
        have h1 : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith only [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
        have h2 : (Real.sin θ) ^ 2 * |Work.Construction.FK F s| * |F s θ|
            ≤ 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul h1 hFKF (abs_nonneg _) (by norm_num)) (hFval θ hθ)
            (abs_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 1) hQfac)
        have h3 : 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q) ≤ 2 * (CFs + 1) ^ 2 * Q := by
          have hnn : 0 ≤ (CFs + 1) ^ 2 := by positivity
          calc 1 * ((CFs + 1) * Q) * ((CFs + 1) * Q)
              = (CFs + 1) ^ 2 * (Q * Q) := by ring
            _ ≤ (CFs + 1) ^ 2 * (2 * Q) := mul_le_mul_of_nonneg_left hQQ hnn
            _ ≤ 2 * (CFs + 1) ^ 2 * Q := by nlinarith only [hnn, hQ0]
        exact le_trans h2 h3
      -- ## the whole block
      have hexp : Work.Construction.N α F Φg s θ
          = (2 * Work.Construction.Rop α Ψ s θ * F s θ)
            + (-(2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ))
            + (-(2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ))
            + (-((1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
                * Work.Spaces.pth F s θ))
            + (-((Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ)) := by
        rw [hΨdef, hFdef]
        simp only [Work.Construction.N, Work.Construction.s2]
        ring
      have hNbd : |Work.Construction.N α F Φg s θ| ≤ 100 * (CFs + 1) ^ 2 * Q := by
        rw [hexp]
        have h := abs_five_le (2 * Work.Construction.Rop α Ψ s θ * F s θ)
          (-(2 * Work.Construction.Uop α Ψ s θ * Work.Spaces.pth F s θ))
          (-(2 * α * Work.Construction.Vop Ψ s θ * Work.Spaces.Dz F s θ))
          (-((1/2) * Work.Construction.s2 θ * Work.Construction.FK F s
              * Work.Spaces.pth F s θ))
          (-((Real.sin θ) ^ 2 * Work.Construction.FK F s * F s θ))
        simp only [abs_neg] at h
        have hsum : 26 * ((CFs + 1) * Q) + 26 * ((CFs + 1) * Q) + 26 * ((CFs + 1) * Q)
            + (CFs + 1) ^ 2 * Q + 2 * (CFs + 1) ^ 2 * Q ≤ 100 * (CFs + 1) ^ 2 * Q := by
          have h2 : (CFs + 1) ≤ (CFs + 1) ^ 2 := by nlinarith only [hCFs0]
          nlinarith only [h2, hQ0]
        linarith only [h, hU1, hU2, hU3, hU4, hU5, hsum]
      have hfin : Work.Spaces.K θ * |Work.Construction.N α F Φg s θ|
          ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
        have h1 : Work.Spaces.K θ * |Work.Construction.N α F Φg s θ|
            ≤ Work.Spaces.K θ * (100 * (CFs + 1) ^ 2 * Q) :=
          mul_le_mul_of_nonneg_left hNbd hK0
        have h2 : Work.Spaces.K θ * (100 * (CFs + 1) ^ 2 * Q)
            ≤ (2 * Real.cos θ) * (100 * (CFs + 1) ^ 2 * Q) :=
          mul_le_mul_of_nonneg_right hKle (by positivity)
        have h3 : (2 * Real.cos θ) * (100 * (CFs + 1) ^ 2 * Q)
            = 200 * (CFs + 1) ^ 2 * Q * Real.cos θ := by ring
        have h4 : 200 * (CFs + 1) ^ 2 * Q * Real.cos θ
            ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
          have hA0 : 0 ≤ 200 * (CFs + 1) ^ 2 := by positivity
          have hcos0' : 0 ≤ Q * Real.cos θ := mul_nonneg hQ0 hc0
          have h5 : 200 * (CFs + 1) ^ 2 * 1 ≤ 200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B)) :=
            mul_le_mul_of_nonneg_left hA1 hA0
          have h6 : (200 * (CFs + 1) ^ 2 * 1) * (Q * Real.cos θ)
              ≤ (200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B))) * (Q * Real.cos θ) :=
            mul_le_mul_of_nonneg_right h5 hcos0'
          have h7 : (200 * (CFs + 1) ^ 2 * 1) * (Q * Real.cos θ)
              = 200 * (CFs + 1) ^ 2 * Q * Real.cos θ := by ring
          have h8 : (200 * (CFs + 1) ^ 2 * ((1 + C₀) * (1 + B))) * (Q * Real.cos θ)
              = 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by ring
          linarith only [h6, h7, h8]
        linarith only [h1, h2, h3, h4]
      have hCb : 200 * (CFs + 1) ^ 2
          ≤ 200 * (CFs + 1) ^ 2 + 400 := by linarith
      calc Work.Spaces.K θ * |Work.Construction.N α
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ) s θ|
          = Work.Spaces.K θ * |Work.Construction.N α F Φg s θ| := by
            rw [hFdef, hΦgdef]
        _ ≤ 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * Q * Real.cos θ := hfin
        _ = 200 * (CFs + 1) ^ 2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
            rw [hQdef, hHdef]
        _ ≤ (200 * (CFs + 1) ^ 2 + 400) * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)
              * Real.cos θ := by
            have h0 : 0 ≤ (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
              rw [← hQdef]
              exact mul_nonneg (mul_nonneg (mul_nonneg h1C h1B) hQ0) hc0
            nlinarith only [hCb, h0]

end Work.FTS.StrongEps.E5Aux2
