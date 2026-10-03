/-
# `Submission.Work.FIArea5.S16Hecke.conv_defs`

Auxiliary sequence vocabulary for the prime-power evaluation of the four-fold Dirichlet
convolution `λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}` of Hecke eigenvalue sequences
(`conv_prime_pow`).

* `gc c` — the geometric sequence `n ↦ c^n`;
* `GabC a b` — the complex coefficient sequence of `1/((1-T)(1-aT)(1-bT)(1-abT))`, i.e. the
  four-fold Cauchy product (`cvs`, from `hecke_prod_local`) of the geometric sequences of
  `1, a, b, ab`; its real version is `Gab` (`hecke_prod_local`, `Gab_nonneg`), which is the
  local factor of the four-fold product of Hecke `L`-series.
* `db f` — the "doubled index" sequence `n ↦ f(n/2)` for even `n`, `0` for odd `n`; it carries
  the local factor `1/(1 - xT²)` of an inert prime.
* `deltaC` — the Kronecker delta, the `p = 2` local factor.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.hecke_prod_local
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- The geometric sequence `n ↦ c^n` over `ℂ`. -/
def gc (c : ℂ) : ℕ → ℂ := fun n => c ^ n

/-- The coefficient sequence of `1/((1-T)(1-aT)(1-bT)(1-abT))`, as a complex sequence. -/
def GabC (a b : ℂ) : ℕ → ℂ := cvs (cvs (cvs (gc 1) (gc a)) (gc b)) (gc (a * b))

/-- Doubled indices: `db f n = f (n/2)` for even `n`, `0` for odd `n`. -/
def db (f : ℕ → ℂ) : ℕ → ℂ := fun n => if Even n then f (n / 2) else 0

/-- The Kronecker delta sequence. -/
def deltaC : ℕ → ℂ := fun n => if n = 0 then 1 else 0

/-- At weight `0` the Größencharacter is just `χ`. -/
lemma psi_zero (chi : GaussianInt → ℂ) (z : GaussianInt) : psi chi 0 z = chi z := by
  rw [psi, zpow_zero, mul_one]

/-- `cvs` of two geometric sequences is the sum over compositions `x^a y^{ν-a}`. -/
lemma cvs_gc_geo (x y : ℂ) : cvs (gc x) (gc y) = geo x y := rfl

/-- `cvs` of real sequences, read in `ℂ`. -/
lemma cvs_ofReal (f g : ℕ → ℝ) (n : ℕ) :
    cvs (fun k => ((f k : ℝ) : ℂ)) (fun k => ((g k : ℝ) : ℂ)) n = ((cvs f g n : ℝ) : ℂ) := by
  simp only [cvs, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The inert local sequence `geoInert x` is `db (gc x)`. -/
lemma geoInert_eq_db (x : ℂ) : geoInert x = db (gc x) := rfl

/-- The Kronecker delta is idempotent for `cvs`. -/
lemma cvs_delta : cvs deltaC deltaC = deltaC := by
  funext n
  rcases n with _ | m
  · simp [cvs, deltaC]
  · rw [cvs]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h : i = 0
    · subst h; simp [deltaC]
    · simp [deltaC, h]

end

end Work.FIArea5.S16Hecke
