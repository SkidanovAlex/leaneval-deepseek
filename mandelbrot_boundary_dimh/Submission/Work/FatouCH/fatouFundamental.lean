import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.backward_iterate
import Submission.Work.FatouCH.strip_injOn
import Submission.Work.FatouCH.forward_iterate

/-!
# Shishikura A.2.1(i): the fundamental strip of a near-translation

This file assembles `MandelDim.FatouFundamental` (Prop. A.2.1(i) of Shishikura, Annals 1998)
from three independent pieces, each proved in a sibling file of this directory:

* `Work.FatouCH.strip_injOn` : `F` is injective on the vertical strip `x₀ - 1 < Re < x₀ + 3`
  (the mean value inequality applied to `F - id`);
* `Work.FatouCH.forward_iterate` : forward iteration from `Re z < x₀` reaches the line
  `Re = x₀` inside `Qreg b₁ b₂`;
* `Work.FatouCH.backward_iterate` : backward iteration from `Re z ≥ x₀` reaches `fundStrip`.

The strip is the only place where injectivity is consumed, which is why the weaker
`strip_injOn` suffices in place of the global `MandelDim.FatouInjOnQ`.
-/

namespace Work.FatouCH

open MandelDim

noncomputable section

/-! ## Elementary geometry -/

/-- Component bounds for one step of a near-translation: `Re` moves by between `31/32`
and `33/32`. -/
lemma re_step_bounds {F : ℂ → ℂ} {u : ℂ} (h : ‖F u - (u + 1)‖ ≤ 1 / 32) :
    u.re + 31 / 32 ≤ (F u).re ∧ (F u).re ≤ u.re + 33 / 32 := by
  have h1 : |(F u - (u + 1)).re| ≤ 1 / 32 := le_trans (Complex.abs_re_le_norm _) h
  have h2 : (F u - (u + 1)).re = (F u).re - u.re - 1 := by simp [Complex.sub_re]; ring
  rw [h2] at h1
  have h3 := abs_le.mp h1
  constructor <;> linarith

/-- The vertical strip `x₀ - 1 < Re z < x₀ + 3` is contained in `Qreg b₁ b₂` as soon as `x₀` is
at least `1` to the right of `b₁` and at least `3` to the left of `b₂`. -/
lemma strip_mem_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {z : ℂ} (hz₁ : x₀ - 1 < z.re) (hz₂ : z.re < x₀ + 3) : z ∈ Qreg b₁ b₂ := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha' := h₁ a ha
    have hpos : 0 < (z - a).re := by simp [Complex.sub_re]; linarith
    have hle : -|(z - a).im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
    linarith
  · intro b hb
    have hb' := h₂ b hb
    have hneg : (z - b).re < 0 := by simp [Complex.sub_re]; linarith
    have hle : 0 ≤ |(z - b).im| := abs_nonneg _
    linarith

/-! ## The main statement -/

/-- Shishikura Prop A.2.1(i), the fundamental strip of the near-translation `F` on `Qreg b₁ b₂`:
with `x₀` a vertical line inside `𝒬`, every point of `𝒬` has an orbit point in `fundStrip F 𝒬 x₀`,
reached by forward or by backward iteration inside `𝒬`.

Proof plan. (1) Geometry: `IsOpen (Qreg b₁ b₂)`; `Qreg ⊇ {Re b₁ < Re < Re b₂}`; for `z ∈ 𝒬` with
`u = z - b₁` the quantity `u.re + |u.im|` increases under `F` because `F z = z + 1 + ε` with
`‖ε‖ ≤ 1/32` (writing `F z - z - 1 = ε`), so a forward orbit starting in `𝒬` never enters the left
cone `{u.re + |u.im| ≤ 0}`; while a forward orbit has `re < Re b₂` it stays in `𝒬` (the right cone
needs `re ≥ |Im|`). Dually a backward orbit stays in `𝒬` while `re > Re b₁`, each inverse step
lowering `re` by between `31/32` and `33/32`. (2) Existence of the strip point, by a monotone-`re`
iteration (no Banach fixed point is needed): if `re z ≥ x₀` and `z ∉ fundStrip`, then by definition
`z` has a `𝒬`-preimage `w` with `re w ≥ x₀` and `re w ≤ re z - 31/32`; iterate this rule — the
`re`-values strictly decrease, so the iteration stops after at most `⌈32 (re z - x₀)/31⌉` steps, and
since every point produced has `re ≥ x₀` the stop point lies in `fundStrip`; that gives the backward
disjunct. If `re z < x₀`, iterate forward while `re < x₀` (the orbit stays in `𝒬`: it never enters
the left cone and has `re < x₀ + 33/32 < Re b₂`) and let `s` be the first point with `re ≥ x₀`. Then
`s ∈ fundStrip`, because the previous iterate is a `𝒬`-preimage of `s`, so by injectivity of `F` on
`𝒬` every `𝒬`-preimage of `s` equals it and has `re < x₀`. Injectivity of `F` on `𝒬` is
`MandelDim.FatouInjOnQ` (Shishikura A.2.1(0)); it is being proved in parallel at
`Submission/Work/FatouCH/fatouInjOnQ` — check whether that module exists and import it, otherwise
prove the injectivity yourself here as a helper. -/
theorem fatouFundamental : MandelDim.FatouFundamental := by
  intro b₁ b₂ F x₀ hadm hF h₁ h₂ z hz
  by_cases hx : x₀ ≤ z.re
  · -- `z` is already to the right of the line: iterate backwards
    obtain ⟨k, s, hs, hsk, hQ⟩ :=
      backward_iterate (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hF hz hx
    exact ⟨k, s, hs, Or.inr ⟨hQ, hsk⟩⟩
  · -- `z` is to the left of the line: iterate forwards
    have hzx : z.re < x₀ := lt_of_not_ge hx
    obtain ⟨k, -, hQ, hkx, hprev⟩ :=
      forward_iterate (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) h₁ h₂ hF hz hzx
    refine ⟨k, F^[k] z, ?_, Or.inl ⟨hQ, rfl⟩⟩
    have hkQ : F^[k] z ∈ Qreg b₁ b₂ := hQ k le_rfl
    refine ⟨hkQ, hkx, ?_⟩
    -- every `Q`-preimage of the landing point is strictly to the left of the line
    intro w hwQ hw
    by_contra hcon
    have hwge : x₀ ≤ w.re := not_lt.mp hcon
    have hkne : k ≠ 0 := by
      rintro rfl
      simp only [Function.iterate_zero, id] at hkx
      linarith
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
    set v : ℂ := F^[m] z with hvdef
    have hvQ : v ∈ Qreg b₁ b₂ := by
      rw [hvdef]; exact hQ m (Nat.le_succ m)
    have hvre : v.re < x₀ := by
      rw [hvdef]; exact hprev m (Nat.lt_succ_self m)
    have hFv : F v = F^[m + 1] z := by
      rw [hvdef, Function.iterate_succ_apply']
    have hFvw : F v = F w := by rw [hFv, hw]
    have hbnd : ∀ u ∈ Qreg b₁ b₂, ‖F u - (u + 1)‖ ≤ 1 / 32 := fun u hu => (hF.2 u hu).1
    have hv_eps := hbnd v hvQ
    have hw_eps := hbnd w hwQ
    have hdist : ‖v - w‖ ≤ 1 / 16 := by
      have heq : v - w = (F w - (w + 1)) - (F v - (v + 1)) := by rw [← hFvw]; ring
      rw [heq]
      calc ‖(F w - (w + 1)) - (F v - (v + 1))‖
          ≤ ‖F w - (w + 1)‖ + ‖F v - (v + 1)‖ := norm_sub_le _ _
        _ ≤ 1 / 32 + 1 / 32 := by linarith
        _ = 1 / 16 := by norm_num
    have hFwre : w.re ≤ (F^[m + 1] z).re - 31 / 32 := by
      have := (re_step_bounds hw_eps).1
      rw [hw] at this
      linarith
    have hsz_upper : (F^[m + 1] z).re ≤ v.re + 33 / 32 := by
      have := (re_step_bounds hv_eps).2
      rw [hFv] at this
      exact this
    have hw_upper : w.re < x₀ + 1 / 16 := by linarith
    have hv_lower : x₀ - 1 / 16 ≤ v.re := by
      have habs : |(v - w).re| ≤ 1 / 16 := le_trans (Complex.abs_re_le_norm (v - w)) hdist
      have h4 := abs_le.mp habs
      simp only [Complex.sub_re] at h4
      linarith
    have hmem_v : v ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := ⟨by linarith, by linarith⟩
    have hmem_w : w ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := ⟨by linarith, by linarith⟩
    have hvw : v = w := strip_injOn h₁ h₂ hF hmem_v hmem_w hFvw
    rw [hvw] at hvre
    linarith

end

end Work.FatouCH
