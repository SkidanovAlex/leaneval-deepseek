/-
# `Work.FIArea7.addChar_extends_charMod4d` — *FI* §16: the additive characters of the Gaussian
unit group `(ℤ[i]/4d)^*` are exactly the `IsCharMod4d`-characters of `ℤ[i]`

The paper's §16 works with the multiplicative characters of `(ℤ[i]/4d)^*`, extended by zero off the
units.  The finite-Fourier expansion `char_expansion_pair` (FI (16.11)/(16.15)/(17.10)) however
indexes its characters by *additive* characters of the unit group `G = (ℤ[i]/4d)^*`:
`Additive G →+ ℂ`, i.e. `χ : AddChar (Additive G) ℂ`.  This file exhibits, for such an additive
character, a function `chi : ℤ[i] → ℂ` with

* `IsCharMod4d d chi` — multiplicative, trivial mod `4d`, bounded by `1`, normalised by `chi 1 = 1`
  and vanishing on the multiples of `4d`;
* `chi z = 0` whenever `(gnorm z, 4d) ≠ 1`, i.e. off the units mod `4d`;
* `chi` evaluated at the canonical lift of `p ∈ G` reproduces `χ (Additive.ofMul p)`.

The construction is the obvious one.  `G` is the coordinate model of the Gaussian unit group
(`GaussUnits.gaussUnitsCommGroup`): `(r,s)` with `r² + s²` a unit of `ZMod n`, product `gaussMul`.
The ring map of the model is the reduction
`phiCoord n z = (z.re mod n, z.im mod n)`, which is compatible with `gaussMul`
(`phiCoord_mul`) and carries the Gaussian norm to `gnorm z mod n` (`gaussNorm_phiCoord`).  So put

  `chi z = χ (Additive.ofMul ⟨phiCoord n z, _⟩)`   if `gaussNorm (phiCoord n z)` is a unit, else `0`.

Every axiom of `IsCharMod4d` is then a transplantation of the corresponding law of `χ` along the
ring map, the units being preserved because `gaussNorm` is multiplicative.
-/
import Mathlib
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.char_expansion_pair
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.card_charMod4d_eq_card_units

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

noncomputable section

/-- The coordinates of `z = re + im·i` reduced modulo `n`: `(re mod n, im mod n)` in `(ZMod n)²`. -/
def phiCoord (n : ℕ) (z : GaussianInt) : ZMod n × ZMod n :=
  ((z.re : ZMod n), (z.im : ZMod n))

/-- The reduction `phiCoord n` is a ring map onto the coordinate model `(ZMod n)²` with the
Gaussian product `gaussMul`. -/
lemma phiCoord_mul (n : ℕ) (z w : GaussianInt) :
    phiCoord n (z * w) = gaussMul (phiCoord n z) (phiCoord n w) := by
  ext <;> simp only [phiCoord, gaussMul, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> push_cast <;> ring

/-- The Gaussian norm of the reduced coordinates is `gnorm z` reduced modulo `n`. -/
lemma gaussNorm_phiCoord (n : ℕ) (z : GaussianInt) :
    gaussNorm (phiCoord n z) = ((Work.FIPlan.gnorm z : ℕ) : ZMod n) := by
  simp only [phiCoord, gaussNorm]
  exact (Work.FIArea7.gnorm_cast n z).symm

/-- The character of `ℤ[i]` attached to an additive character `χ` of the Gaussian unit group
`(ℤ[i]/n)^*`: reduce `z` modulo `n`; if the reduction is a unit, evaluate `χ` at it, otherwise
return `0`. -/
noncomputable def chiOf (n : ℕ)
    (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ) :
    GaussianInt → ℂ := by
  classical
  exact fun z => if h : IsUnit (gaussNorm (phiCoord n z)) then
    χ (Additive.ofMul ⟨phiCoord n z, h⟩) else 0

variable {n : ℕ} [NeZero n]

/-- `chiOf` takes the value `1` at `1`. -/
lemma chiOf_one (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ) :
    chiOf n χ 1 = 1 := by
  classical
  rw [chiOf]
  have h1 : phiCoord n (1 : GaussianInt) = ((1 : ZMod n), (0 : ZMod n)) := by
    simp [phiCoord]
  have hu : IsUnit (gaussNorm (phiCoord n (1 : GaussianInt))) := by
    rw [h1]; simp [gaussNorm]
  rw [dif_pos hu]
  have hone : (⟨phiCoord n (1 : GaussianInt), hu⟩ :
      {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) = 1 := Subtype.ext h1
  rw [hone]
  exact AddChar.map_zero_eq_one χ

/-- `chiOf` is multiplicative: the reduction is a ring map (`phiCoord_mul`) and units are preserved
because `gaussNorm` is multiplicative (`gaussNorm_gaussMul`). -/
lemma chiOf_mul (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ)
    (z w : GaussianInt) : chiOf n χ (z * w) = chiOf n χ z * chiOf n χ w := by
  classical
  rw [chiOf, chiOf, chiOf]
  by_cases hz : IsUnit (gaussNorm (phiCoord n z))
  · by_cases hw : IsUnit (gaussNorm (phiCoord n w))
    · have hzw : IsUnit (gaussNorm (phiCoord n (z * w))) := by
        rw [phiCoord_mul, gaussNorm_gaussMul]; exact hz.mul hw
      rw [dif_pos hz, dif_pos hw, dif_pos hzw]
      have hmul : (⟨phiCoord n (z * w), hzw⟩ :
          {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) =
          ⟨phiCoord n z, hz⟩ * ⟨phiCoord n w, hw⟩ := by
        apply Subtype.ext
        show phiCoord n (z * w) = gaussMul (phiCoord n z) (phiCoord n w)
        rw [phiCoord_mul]
      rw [hmul, ofMul_mul, AddChar.map_add_eq_mul]
    · have hzw : ¬ IsUnit (gaussNorm (phiCoord n (z * w))) := by
        intro h
        rw [phiCoord_mul, gaussNorm_gaussMul] at h
        exact hw (isUnit_of_dvd_unit (dvd_mul_left _ _) h)
      rw [dif_pos hz, dif_neg hw, dif_neg hzw, mul_zero]
  · have hzw : ¬ IsUnit (gaussNorm (phiCoord n (z * w))) := by
      intro h
      rw [phiCoord_mul, gaussNorm_gaussMul] at h
      exact hz (isUnit_of_dvd_unit (dvd_mul_right _ _) h)
    rw [dif_neg hz, dif_neg hzw, zero_mul]

/-- `chiOf` is bounded by `1`: on the finite group of Gaussian units an additive character takes
values of modulus `1` (`AddChar.norm_apply`), and off the units it is `0`. -/
lemma chiOf_norm_le (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ)
    (z : GaussianInt) : ‖chiOf n χ z‖ ≤ 1 := by
  classical
  rw [chiOf]
  split_ifs with h
  · rw [AddChar.norm_apply]
  · simp

/-- `chiOf` is trivial modulo `n`: `n ∣ z - w` makes the reductions `phiCoord n` equal. -/
lemma chiOf_periodic (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ)
    {z w : GaussianInt} (h : (((n : ℕ) : ℤ) : GaussianInt) ∣ z - w) :
    chiOf n χ z = chiOf n χ w := by
  classical
  obtain ⟨hre, him⟩ := Work.FIArea7.casts_eq_of_dvd (N := n) h
  rw [chiOf, chiOf]
  have : phiCoord n z = phiCoord n w := by
    simp only [phiCoord]; rw [hre, him]
  rw [this]

/-- `chiOf` vanishes on the multiples of `n`: these reduce to `0`, whose norm `0` is not a unit. -/
lemma chiOf_eq_zero_of_dvd [Fact (1 < n)]
    (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ) {z : GaussianInt}
    (h : (((n : ℕ) : ℤ) : GaussianInt) ∣ z) : chiOf n χ z = 0 := by
  classical
  rw [chiOf, dif_neg]
  intro hu
  obtain ⟨hre, him⟩ := Work.FIArea7.casts_eq_of_dvd (N := n) (z := z) (w := 0) (by simpa using h)
  have hz : phiCoord n z = (0, 0) := by
    simp only [phiCoord]; rw [hre, him]; simp
  rw [hz] at hu
  simp only [gaussNorm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hu
  exact not_isUnit_zero hu

/-- `chiOf` vanishes off the units modulo `n`, i.e. on the `z` with `(gnorm z, n) ≠ 1`
(`ZMod.isUnit_iff_coprime`). -/
lemma chiOf_eq_zero_of_not_coprime
    (χ : AddChar (Additive {p : ZMod n × ZMod n // IsUnit (gaussNorm p)}) ℂ) {z : GaussianInt}
    (h : ¬ Nat.Coprime (Work.FIPlan.gnorm z) n) : chiOf n χ z = 0 := by
  classical
  rw [chiOf, dif_neg]
  intro hu
  rw [gaussNorm_phiCoord] at hu
  exact h ((ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z) n).mp hu)

/-- The canonical lift of `p : (ℤ[i]/n)^*` back to `ℤ[i]` reproduces the value of `χ`. -/
lemma chiOf_ofMul_eq (d : ℕ) (hd : 0 < d)
    (χ : AddChar (Additive {p : ZMod (4 * d) × ZMod (4 * d) //
        IsUnit (gaussNorm p)}) ℂ)
    (p : {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (gaussNorm p)}) :
    χ (Additive.ofMul p) = chiOf (4 * d) χ ⟨(p.1.1.val : ℤ), (p.1.2.val : ℤ)⟩ := by
  haveI hn : NeZero (4 * d) := ⟨by omega⟩
  classical
  rw [chiOf]
  have hp : phiCoord (4 * d) (⟨(p.1.1.val : ℤ), (p.1.2.val : ℤ)⟩ : GaussianInt) = p.1 := by
    simp only [phiCoord]
    ext
    · show (((p.1.1.val : ℤ)) : ZMod (4 * d)) = p.1.1
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    · show (((p.1.2.val : ℤ)) : ZMod (4 * d)) = p.1.2
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit
      (gaussNorm (phiCoord (4 * d) (⟨(p.1.1.val : ℤ), (p.1.2.val : ℤ)⟩ : GaussianInt))) := by
    rw [hp]; exact p.2
  rw [dif_pos hu]
  rw [show (⟨phiCoord (4 * d) (⟨(p.1.1.val : ℤ), (p.1.2.val : ℤ)⟩ : GaussianInt), hu⟩ :
      {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (gaussNorm p)}) = p from Subtype.ext hp]

theorem addChar_extends_charMod4d (d : ℕ) (hd : 0 < d)
    (χ : AddChar (Additive {p : ZMod (4 * d) × ZMod (4 * d) //
        IsUnit (Work.FIArea7.gaussNorm p)}) ℂ) :
    ∃ chi : GaussianInt → ℂ,
      (Work.FITop3.IsCharMod4d d chi ∧
        (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0)) ∧
      ∀ p : {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (Work.FIArea7.gaussNorm p)},
        χ (Additive.ofMul p)
          = chi ⟨((p.1.1.val : ℤ)), ((p.1.2.val : ℤ))⟩ := by
  haveI hn : NeZero (4 * d) := ⟨by omega⟩
  haveI hf : Fact (1 < 4 * d) := ⟨by omega⟩
  refine ⟨chiOf (4 * d) χ, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact chiOf_one χ
  · intro z w; exact chiOf_mul χ z w
  · exact chiOf_norm_le χ
  · intro z w hzw; exact chiOf_periodic χ hzw
  · intro z hz; exact chiOf_eq_zero_of_dvd χ hz
  · intro z hz; exact chiOf_eq_zero_of_not_coprime χ hz
  · intro p; exact chiOf_ofMul_eq d hd χ p

end

end Work.FIArea7
