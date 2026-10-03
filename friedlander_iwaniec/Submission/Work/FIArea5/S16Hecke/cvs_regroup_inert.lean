import Mathlib
import Submission.Work.FIArea5.S16Hecke.conv_defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- The "doubled index" sequence `db f` is the expansion `X ↦ X²` of the generating
power series of `f`: replacing `X` by `X²` inserts a zero in every odd position. -/
lemma mk_db (f : ℕ → ℂ) :
    PowerSeries.mk (db f) = (PowerSeries.mk f).expand 2 (by norm_num) := by
  ext n
  simp only [PowerSeries.coeff_expand, PowerSeries.coeff_mk, db, even_iff_two_dvd]

/-- `db` is multiplicative for the Cauchy product: doubling the indices of a convolution is
the convolution of the doubled-index sequences. -/
lemma cvs_db (f g : ℕ → ℂ) : cvs (db f) (db g) = db (cvs f g) := by
  have hmul : (PowerSeries.expand 2 (by norm_num) :
        PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ)
        (PowerSeries.mk f * PowerSeries.mk g)
      = PowerSeries.expand 2 (by norm_num) (PowerSeries.mk f)
        * PowerSeries.expand 2 (by norm_num) (PowerSeries.mk g) :=
    map_mul _ _ _
  have h : PowerSeries.mk (cvs (db f) (db g)) = PowerSeries.mk (db (cvs f g)) := by
    rw [mk_cvs, mk_db, mk_db, mk_db, ← hmul, ← mk_cvs]
  funext n
  simpa [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) h

end

theorem cvs_regroup_inert (r₁ r₂ : ℂ) :
    Work.FIArea5.S16Hecke.cvs
        (Work.FIArea5.S16Hecke.cvs
          (Work.FIArea5.S16Hecke.cvs
            (Work.FIArea5.S16Hecke.db (Work.FIArea5.S16Hecke.gc 1))
            (Work.FIArea5.S16Hecke.db (Work.FIArea5.S16Hecke.gc r₁)))
          (Work.FIArea5.S16Hecke.db (Work.FIArea5.S16Hecke.gc r₂)))
        (Work.FIArea5.S16Hecke.db (Work.FIArea5.S16Hecke.gc (r₁ * r₂)))
      = Work.FIArea5.S16Hecke.db (Work.FIArea5.S16Hecke.GabC r₁ r₂) := by
  unfold GabC
  rw [cvs_db, cvs_db, cvs_db]

end Work.FIArea5.S16Hecke
