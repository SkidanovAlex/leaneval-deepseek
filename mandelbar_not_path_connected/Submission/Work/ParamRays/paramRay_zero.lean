import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.PhiUnique
import Submission.Work.ParamRays.continuous_potential
import Submission.Work.ParamRays.RealSlice
import Submission.Work.ParamRays.Phi_real_pos_of_one_fourth_lt
import Submission.Work.ParamRays.exists_norm_Phi_ofReal_eq_of_one_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

/-- `Φ` is injective on the exterior of the mandelbar: it agrees there with Nakane's
homeomorphism onto `‖w‖ > 1`. -/
theorem Phi_injective_compl (hN : NakaneInput) {c d : ℂ} (hc : c ∉ Mb) (hd : d ∉ Mb)
    (h : Phi c = Phi d) : c = d := by
  obtain ⟨e, he⟩ := Phi_homeo hN
  have h1 : e ⟨c, hc⟩ = e ⟨d, hd⟩ := by
    apply Subtype.ext
    rw [he ⟨c, hc⟩, he ⟨d, hd⟩]
    exact h
  have h2 : e.symm (e ⟨c, hc⟩) = e.symm (e ⟨d, hd⟩) := congrArg e.symm h1
  have h3 : (⟨c, hc⟩ : ↥(Mbᶜ)) = ⟨d, hd⟩ := by simpa using h2
  simpa using congrArg Subtype.val h3

/-- The point of the unit circle of angle `0` is `1`. -/
theorem rayDir_zero : rayDir 0 = 1 := by
  simp [rayDir]

/-- The parameter ray of external angle `0` is the real ray above the root point `1/4`.
Here `hconj` is the conjugation equivariance of `Phi` (`Work.ParamRays.Phi_conj hN.bottcher`).
For real `c > 1/4` the critical orbit is increasing and unbounded, so `c` is outside `Mb`, `hconj`
makes `Phi c` real, `one_lt_norm_Phi` makes its modulus bigger than `1`, and continuity plus the
asymptotic `Phi c / c → 1` fix the positive sign.  Conversely, `Phi` maps `(1/4,∞)` continuously
and injectively into `(1,∞)` with limits `1` at `1/4` (continuity of the potential at the
boundary) and `∞` at infinity, so by the intermediate value property the image is `(1,∞)`, and
injectivity of `Phi` (from `NakaneHomeo`) identifies the preimage of a real `r > 1`. -/
theorem paramRay_zero (hN : Work.ParamRays.NakaneInput)
    (hconj : ∀ c : ℂ, Work.ParamRays.Phi ((starRingEnd ℂ) c) =
      (starRingEnd ℂ) (Work.ParamRays.Phi c)) :
    Work.ParamRays.paramRay 0 = {c : ℂ | c.im = 0 ∧ (1 / 4 : ℝ) < c.re} := by
  -- the two real-axis facts, provided by the companion modules
  have hpos : ∀ x : ℝ, 1 / 4 < x → ∃ r : ℝ, 1 < r ∧ Phi (x : ℂ) = (r : ℂ) :=
    fun x hx => Phi_real_pos_of_one_fourth_lt hN hconj hx
  have hsurj : ∀ r : ℝ, 1 < r → ∃ x : ℝ, 1 / 4 < x ∧ ‖Phi (x : ℂ)‖ = r :=
    fun r hr => exists_norm_Phi_ofReal_eq_of_one_lt hN hr
  have hinj : ∀ {c d : ℂ}, c ∉ Mb → d ∉ Mb → Phi c = Phi d → c = d :=
    fun hc hd h => Phi_injective_compl hN hc hd h
  ext c
  constructor
  · -- a point of the ray of angle `0` is real (by conjugation equivariance and injectivity)
    -- and lies above `1/4` (by surjectivity on the real axis and injectivity)
    rintro ⟨hcmb, r, hr, hPhi⟩
    have hr0 : Phi c = (r : ℂ) := by
      rw [hPhi, rayDir_zero, mul_one]
    have hconjc : Phi ((starRingEnd ℂ) c) = Phi c := by
      rw [hconj c, hr0, Complex.conj_ofReal]
    have hconjmb : (starRingEnd ℂ) c ∉ Mb := by
      intro hmem
      exact hcmb (by simpa using mandelbar_conj (c := (starRingEnd ℂ) c) hmem)
    have hreal : (starRingEnd ℂ) c = c := hinj hconjmb hcmb hconjc
    have him : c.im = 0 := Complex.conj_eq_iff_im.mp hreal
    refine ⟨him, ?_⟩
    obtain ⟨x, hx, hxnorm⟩ := hsurj r hr
    obtain ⟨r', hr', hxPhi⟩ := hpos x hx
    have hr'eq : r' = r := by
      have h : ‖(r' : ℂ)‖ = r := by rw [← hxPhi]; exact hxnorm
      simpa [abs_of_pos (by linarith : (0:ℝ) < r')] using h
    have hxPhi' : Phi (x : ℂ) = (r : ℂ) := by rw [hxPhi, hr'eq]
    have hxc : (x : ℂ) = c := hinj (real_not_mem_Mb_of_one_fourth_lt hx) hcmb (by rw [hxPhi', hr0])
    rw [← hxc]
    simpa using hx
  · -- conversely a real parameter above `1/4` lies on the ray of angle `0`
    rintro ⟨him, hre⟩
    have hcx : c = (c.re : ℂ) := complex_eq_ofReal_re_of_im_zero him
    have hmb : c ∉ Mb := by
      rw [hcx]
      exact real_not_mem_Mb_of_one_fourth_lt hre
    obtain ⟨r, hr, hPhi⟩ := hpos c.re hre
    exact ⟨hmb, r, hr, by rw [hcx, hPhi, rayDir_zero, mul_one]⟩

end Work.ParamRays
