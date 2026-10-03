import Submission.Work.Fatou.FX8.Basic

/-!
# FX8, step 3: `Π` and `Φ` are injective and surjective modulo `ℤ`

* `Pi_inj`: the orbit projection `Π` is injective on `Qreg b₁ b₂` — the canonical parameter of the
  fundamental-strip representative has real part in `[0,1)`, which pins down the level.
* `exists_Pi`: `Π` is onto modulo `ℤ` (take `ζ = ξ - ⌊Re ξ⌋`, the fundamental-strip point
  `devH ζ` has `Π`-value `ζ`).
* `Phi_inj`, `exists_Phi`: the same for `Φ = Ψ ∘ Π / b` (`b ≠ 0`, `Ψ` bijective, deck shift `b`).
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

open Work.Fatou

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- **The orbit projection is injective.** -/
theorem Pi_inj (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) {z z' : ℂ} (hz : z ∈ Qreg b₁ b₂) (hz' : z' ∈ Qreg b₁ b₂)
    (h : Pi hadm hF od z = Pi hadm hF od z') : z = z' := by
  have hspec := canonParam_spec hadm hF (od.rep_mem z hz)
  have hspec' := canonParam_spec hadm hF (od.rep_mem z' hz')
  have hmain : canonParam hadm hF (od.rep z) + ((od.lev z : ℤ) : ℂ)
      = canonParam hadm hF (od.rep z') + ((od.lev z' : ℤ) : ℂ) := h
  have hre : (canonParam hadm hF (od.rep z)).re + (od.lev z : ℝ)
      = (canonParam hadm hF (od.rep z')).re + (od.lev z' : ℝ) := by
    have h' := congrArg Complex.re hmain
    simpa only [Complex.add_re, Complex.intCast_re] using h'
  -- the level difference is an integer whose real part lies in `(-1, 1)`
  have hdcast : (od.lev z : ℝ) - (od.lev z' : ℝ) = ((od.lev z - od.lev z' : ℤ) : ℝ) := by
    push_cast; ring
  have hsmall_lo : (-1 : ℝ) < (od.lev z : ℝ) - (od.lev z' : ℝ) := by
    have := hspec.2.1; have := hspec'.1; linarith
  have hsmall_hi : (od.lev z : ℝ) - (od.lev z' : ℝ) < 1 := by
    have := hspec.2.1; have := hspec'.2.1; linarith
  have hlev : od.lev z = od.lev z' := by
    have h1 : ((od.lev z - od.lev z' : ℤ) : ℝ) < 1 := by rw [← hdcast]; exact hsmall_hi
    have h2 : (-1 : ℝ) < ((od.lev z - od.lev z' : ℤ) : ℝ) := by rw [← hdcast]; exact hsmall_lo
    have h1' : od.lev z - od.lev z' < 1 := by exact_mod_cast h1
    have h2' : -1 < od.lev z - od.lev z' := by exact_mod_cast h2
    omega
  have hcp : canonParam hadm hF (od.rep z) = canonParam hadm hF (od.rep z') := by
    have h' := hmain
    rw [hlev] at h'
    exact add_right_cancel h'
  have hrep : od.rep z = od.rep z' :=
    canonParam_inj hadm hF (od.rep_mem z hz) (od.rep_mem z' hz') hcp
  exact od.inj z hz z' hz' hrep hlev

/-- **The orbit projection is onto modulo `ℤ`.** -/
theorem exists_Pi (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F) (ξ : ℂ) :
    ∃ z ∈ Qreg b₁ b₂, ∃ n : ℤ, Pi hadm hF od z = ξ + (n : ℂ) := by
  set n : ℤ := ⌊ξ.re⌋ with hn
  set ζ : ℂ := ξ - (n : ℂ) with hζ
  have hre1 : 0 ≤ ζ.re := by
    rw [hζ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.intCast_re]
    rw [hn]
    have := Int.floor_le ξ.re
    linarith
  have hre2 : ζ.re < 1 := by
    rw [hζ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.intCast_re]
    rw [hn]
    have := Int.lt_floor_add_one ξ.re
    linarith
  have hsf : Work.Fatou.devH (xOf b₁ b₂) F ζ ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂) :=
    (Work.Fatou.Surface.devH_fundStrip hadm hF).1 ζ hre1 hre2
  have hcanon : canonParam hadm hF (Work.Fatou.devH (xOf b₁ b₂) F ζ) = ζ := by
    apply Work.Fatou.devH_injective (Work.Fatou.Surface.devHBound_xOf hadm hF)
    rw [devH_canonParam hadm hF hsf]
  refine ⟨Work.Fatou.devH (xOf b₁ b₂) F ζ, hsf.1, -n, ?_⟩
  rw [Pi_of_fundStrip hadm hF od hsf, hcanon, hζ]
  push_cast
  ring_nf

/-- **The constructed coordinate `Φ` is injective.** -/
theorem Phi_inj {b : ℂ} (hb : b ≠ 0) (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {z z' : ℂ} (hz : z ∈ Qreg b₁ b₂) (hz' : z' ∈ Qreg b₁ b₂)
    (h : Phi hadm hF od Ψ b z = Phi hadm hF od Ψ b z') : z = z' := by
  have hmul : (Phi hadm hF od Ψ b z) * b = (Phi hadm hF od Ψ b z') * b := by rw [h]
  simp only [Phi_apply, div_mul_cancel₀ _ hb] at hmul
  have h1 : (fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)
      = (fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z') := Ψ.injective hmul
  have h2 : Pi hadm hF od z = Pi hadm hF od z' := by
    have := congrArg (fun u => (fatouData b₁ b₂ F hadm hF).toℂ u) h1
    simpa using this
  exact Pi_inj hadm hF od hz hz' h2

/-- **The constructed coordinate `Φ` is onto modulo `ℤ`.** -/
theorem exists_Phi {b : ℂ} (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b) (hb : b ≠ 0) (w : ℂ) :
    ∃ z ∈ Qreg b₁ b₂, ∃ n : ℤ, Phi hadm hF od Ψ b z = w + (n : ℂ) := by
  obtain ⟨z, hz, n, hn⟩ :=
    exists_Pi hadm hF od ((fatouData b₁ b₂ F hadm hF).toℂ (Ψ.symm (b * w)))
  refine ⟨z, hz, n, ?_⟩
  have hstep : (fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)
      = Tpow (fatouData b₁ b₂ F hadm hF) n (Ψ.symm (b * w)) := by
    rw [hn]
    rfl
  rw [Phi_apply, hstep,
    shift_Tpow (D := fatouData b₁ b₂ F hadm hF) hshift n (Ψ.symm (b * w)),
    Ψ.apply_symm_apply]
  field_simp

end

end Work.Fatou.FX8
