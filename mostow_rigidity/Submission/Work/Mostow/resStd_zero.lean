import Mathlib
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.stab_eq_blk

/-!
# `resStd k 0` is the identity

For a zero-dimensional normal space the block decomposition of the stratum stabiliser is trivial:
`blk k 0 h R = h` for every `h : PO k 1` and every `R : E 0 ≃ₗᵢ[ℝ] E 0` (there is in fact only
one such `R`, the identity, and `E 0` is a point).  Consequently the restriction map `resStd k 0`
of the standard stratum `E k ↪ E (k + 0)` — a choice-defined first component of a block
decomposition — returns its argument, since the first component of *any* block decomposition of
`g` is forced to be `g`.

The two geometric inputs are the triviality of the zero padding `coordEmb k 0` (it is the identity
of `E k = E (k + 0)`, up to the definitional identification `k + 0 = k`), and
`Work.Mostow.blk_smul_fermi`, which computes the action of `blk k 0 h R` in Fermi coordinates.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### The zero padding is the identity

`E k` and `E (k + 0)` are definitionally equal (`k + 0` reduces to `k`), so these are honest
equalities; only the `Fin.append`/`Fin.castAdd` bookkeeping of `coordEmb` has to be discharged. -/

private lemma fermi_zero_coordEmb (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  have hs : sinhc (0 : ℝ) = 1 := by rw [sinhc]; norm_num
  simp only [fermi, coordEmb, norm_zero, Real.cosh_zero, hs, one_mul]
  congr 1

private lemma coordEmb_zerodim (k : ℕ) (v : E k) : coordEmb k 0 v = v := by
  ext i
  change Fin.append (fun j : Fin k => v j) (fun _ : Fin 0 => (0 : ℝ)) i = v i
  rw [show i = Fin.castAdd 0 i from rfl]
  exact Fin.append_left _ _ i

/-! ### The block of a zero-dimensional normal space is the foot map -/

/-- `blk k 0 h R = h`: with a zero-dimensional normal space the block isometry is the foot map. -/
theorem blk_zero (k : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + 0)) (hI : HypIsometryProp (k + 0))
    (h : PO k 1) (R : E 0 ≃ₗᵢ[ℝ] E 0) : blk k 0 h R = h := by
  -- both act in the same way on `E (k + 0)`; in Fermi coordinates the normal component is
  -- forced to vanish, and the zero padding identifies `blk` with `h`.
  have hfix : ∀ u : E (k + 0), (blk k 0 h R) • u = h • u := by
    intro u
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi k 0 v w := ⟨_, _, ((fermi_inv k 0).2.1 u).symm⟩
    rw [blk_smul_fermi k 0 hAk hIk hA hI h R v w]
    have hw : w = 0 := Subsingleton.elim w 0
    rw [hw, R.map_zero]
    rw [fermi_zero_coordEmb, fermi_zero_coordEmb, coordEmb_zerodim, coordEmb_zerodim]
  -- faithfulness: `h⁻¹ * blk k 0 h R` acts trivially
  have h1 : h⁻¹ * blk k 0 h R = 1 := hA.2.2.2.2.2.1 _ (fun u => by
    rw [hA.2.2.2.2.1 h⁻¹ (blk k 0 h R) u, hfix u, ← hA.2.2.2.2.1 h⁻¹ h u, inv_mul_cancel,
      hA.2.2.2.1])
  have h2 := congrArg (fun x => h * x) h1
  rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2

/-- Any first component of a block decomposition of `g` is `g` itself in normal dimension `0`. -/
private lemma eq_of_eq_blk_zero {k : ℕ} (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + 0)) (hI : HypIsometryProp (k + 0)) (g : PO (k + 0) 1)
    (h : PO k 1) (R : E 0 ≃ₗᵢ[ℝ] E 0) (hg : g = blk k 0 h R) : h = g :=
  (hg.trans (blk_zero k hAk hIk hA hI h R)).symm

theorem resStd_zero (k : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (hIk : Submission.Mostow.HypIsometryProp k) (hA : Submission.Mostow.POActionProp (k + 0))
    (hI : Submission.Mostow.HypIsometryProp (k + 0))
    (g : LeanEval.Geometry.MostowRigidity.PO (k + 0) 1) :
    Submission.Mostow.resStd k 0 g = g := by
  have hb : ∀ (h : PO k 1) (R : E 0 ≃ₗᵢ[ℝ] E 0), blk k 0 h R = h :=
    blk_zero k hAk hIk hA hI
  have hex : ∃ p : PO k 1 × (E 0 ≃ₗᵢ[ℝ] E 0), g = blk k 0 p.1 p.2 :=
    ⟨(g, 1), (hb g 1).symm⟩
  unfold Submission.Mostow.resStd
  rw [dite_eq_left hex]
  exact eq_of_eq_blk_zero hAk hIk hA hI g _ _ hex.choose_spec

end

end Work.Mostow
