/-
# `Submission.Work.FIArea7.dirichletSym_periodic` — periodicity of the Dirichlet symbol

`ξ_w(z) = (Re(w z) | |w|²)` (19.9)–(19.11) is a character of `ℤ[i]/|w|²ℤ[i]`, hence periodic with
any period divisible by `|w|²`.  This is the interface that lets the orthogonality relation of §21
(Lemma 21.1) be stated with `ζ` ranging over `ZMod q × ZMod q` (i.e. over `ℤ[i]/qℤ[i]`) and
`(ζ/w)` meaning `Work.FIArea7.DirichletSym w ζ` for `|w|² ∣ q`.
-/
import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`ξ_w` is periodic with any period divisible by `|w|²`**: if `m` is a multiple of `|w|²` and
`z ≡ z' (mod m)` in `ℤ[i]` (i.e. `m` divides `z − z'`), then `ξ_w(z) = ξ_w(z')`.

Indeed `Re(w z) ≡ Re(w z') (mod m)` (apply `Re` to `w(z − z') = m·c`), hence modulo `|w|²` as
well, and `jacobiSym (·) |w|²` depends only on the residue class modulo `|w|²`
(`jacobiSym.mod_left`). -/
theorem dirichletSym_periodic {w z z' : GaussianInt} {m : ℕ} (hm : Work.FIPlan.gnorm w ∣ m)
    (hz : (((m : ℕ) : ℤ) : GaussianInt) ∣ z - z') :
    DirichletSym w z = DirichletSym w z' := by
  obtain ⟨c, hc⟩ := hz
  have h1 : w * z - w * z' = (((m : ℕ) : ℤ) : GaussianInt) * (w * c) := by
    rw [← mul_sub, hc]; ring
  have hre : (((m : ℕ) : ℤ)) ∣ (w * z).re - (w * z').re := by
    have h := congrArg Zsqrtd.re h1
    rw [Zsqrtd.re_sub, Zsqrtd.re_smul] at h
    exact ⟨(w * c).re, h⟩
  have hcast : (((Work.FIPlan.gnorm w : ℕ) : ℤ)) ∣ (((m : ℕ) : ℤ)) := by
    exact_mod_cast hm
  have hdvd : (((Work.FIPlan.gnorm w : ℕ) : ℤ)) ∣ (w * z).re - (w * z').re :=
    hcast.trans hre
  have hmod : (w * z).re ≡ (w * z').re [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    simpa using (dvd_neg.mpr hdvd :
      (((Work.FIPlan.gnorm w : ℕ) : ℤ)) ∣ -((w * z).re - (w * z').re))
  rw [DirichletSym, DirichletSym, jacobiSym.mod_left (w * z).re (Work.FIPlan.gnorm w), hmod,
    ← jacobiSym.mod_left (w * z').re (Work.FIPlan.gnorm w)]

end

end Work.FIArea7
