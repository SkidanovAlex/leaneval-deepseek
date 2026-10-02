/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The enclosure of `‖z‖²` and of products of intervals over a complex box

`CBox.normSq B` is a real interval containing `‖z‖²` for every `z ∈ B`; `IV.prod l` is the hull of
a list of intervals.  These are the two ingredients of the third equation
`P₃ = ∏_{k<5} ‖T_c^k z‖² - 2^{-10}` of `NOTES_LEAD_mandelbar_noncusp.md` §2.2 (item A1), and of the
petal-entry check (D3) of §2.4, whose test `Re (-1/(A (z - z₁))) < -R` is evaluated with the same
box arithmetic.
-/
import ChallengeDeps
import Submission.Work.SeedCertNum.TBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

/-- Soundness of `IV.sq` (the corner hull of the product with itself). -/
theorem IV.mem_sq {I : IV} {x : ℝ} (hx : x ∈ I.toSet) : x ^ 2 ∈ (I.sq).toSet := by
  rw [IV.sq, pow_two]
  exact Work.SeedCertNum.IV_mem_mul hx hx

/-- The interval `‖z‖² = z.re² + z.im²` over the box `B`. -/
def CBox.normSq (B : CBox) : IV := (B.re.sq).add (B.im.sq)

theorem CBox.mem_normSq {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) :
    ‖z‖ ^ 2 ∈ (B.normSq).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hx : z.re ^ 2 ∈ (B.re.sq).toSet := IV.mem_sq ⟨h1, h2⟩
  have hy : z.im ^ 2 ∈ (B.im.sq).toSet := IV.mem_sq ⟨h3, h4⟩
  have h := IV.mem_add hx hy
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rwa [hnorm, CBox.normSq]

/-- The hull of a product of intervals (left-associated). -/
def IV.prod : List IV → IV
  | [] => ⟨Dya.one, Dya.one⟩
  | I :: l => I.mul (IV.prod l)

theorem IV.mem_prod {l : List IV} {f : IV → ℝ} (hx : ∀ I ∈ l, f I ∈ I.toSet) :
    (l.map f).prod ∈ (IV.prod l).toSet := by
  induction l with
  | nil => simp [IV.prod, IV.toSet, Dya.toReal_one]
  | cons I l ih =>
    have hI : f I ∈ I.toSet := hx I (by simp)
    have hl : ∀ J ∈ l, f J ∈ J.toSet := fun J hJ => hx J (by simp [hJ])
    have := Work.SeedCertNum.IV_mem_mul hI (ih hl)
    simpa [IV.prod, List.map_cons, List.prod_cons] using this

end Work.SeedCert
