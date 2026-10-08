import Mathlib
import Submission.Work.L2F.Mat2.det_smul_one_add_smul

namespace Work.L2F.Props.oddsub

theorem eq_one_of_eval_eq_one (F L : Type*) [Field F] [Field L] [Algebra F L]
    (t : Matrix (Fin 2) (Fin 2) F) (lam mu : L)
    (hsum : lam + mu = algebraMap F L t.trace) (hprod : lam * mu = algebraMap F L t.det)
    (hne : lam ≠ mu) (a b : F)
    (haeval : algebraMap F L a + algebraMap F L b * lam = 1)
    (hdet : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • t).det = 1) : a = 1 ∧ b = 0 := by
  -- Determinant identity in `F`: det(a·1 + b·t) = a² + a·b·tr(t) + b²·det(t) = 1.
  have hdet' : a ^ 2 + a * b * t.trace + b ^ 2 * t.det = 1 := by
    rw [← Work.L2F.Mat2.det_smul_one_add_smul F t a b]
    exact hdet
  -- Push the identity to `L`.
  have hmap : algebraMap F L a ^ 2 + algebraMap F L a * algebraMap F L b * algebraMap F L t.trace
      + algebraMap F L b ^ 2 * algebraMap F L t.det = 1 := by
    have h := congrArg (algebraMap F L) hdet'
    simp only [map_add, map_mul, map_pow, map_one] at h
    exact h
  -- `(a + b·λ)(a + b·μ) = a² + a·b·(λ+μ) + b²·(λμ) = a² + a·b·tr(t) + b²·det(t) = 1`.
  have hkey :
      (algebraMap F L a + algebraMap F L b * lam) * (algebraMap F L a + algebraMap F L b * mu)
        = algebraMap F L a ^ 2 + algebraMap F L a * algebraMap F L b * (lam + mu)
            + algebraMap F L b ^ 2 * (lam * mu) := by
    ring
  have hprod_eq :
      (algebraMap F L a + algebraMap F L b * lam) * (algebraMap F L a + algebraMap F L b * mu) = 1 := by
    rw [hkey, hsum, hprod]
    exact hmap
  -- Since `a + b·λ = 1`, the product relation forces `a + b·μ = 1` too.
  have hmu : algebraMap F L a + algebraMap F L b * mu = 1 := by
    have h := hprod_eq
    rw [haeval] at h
    simpa using h
  -- Hence `b·(λ - μ) = 0`, and `λ ≠ μ` gives `b = 0` in `L`.
  have hb_mul : algebraMap F L b * (lam - mu) = 0 := by
    have h1 : algebraMap F L a + algebraMap F L b * lam
        = algebraMap F L a + algebraMap F L b * mu := by
      rw [haeval, hmu]
    have h2 : algebraMap F L b * lam = algebraMap F L b * mu := add_left_cancel h1
    have h3 : algebraMap F L b * lam - algebraMap F L b * mu = 0 := sub_eq_zero.mpr h2
    rwa [← mul_sub] at h3
  have hb_map : algebraMap F L b = 0 := by
    rcases mul_eq_zero.mp hb_mul with h | h
    · exact h
    · exact absurd h (sub_ne_zero.mpr hne)
  have hb : b = 0 := (algebraMap F L).injective (by rw [hb_map, map_zero])
  have ha_map : algebraMap F L a = 1 := by
    have h := haeval
    rw [hb_map] at h
    simpa using h
  have ha : a = 1 := (algebraMap F L).injective (by rw [ha_map, map_one])
  exact ⟨ha, hb⟩

end Work.L2F.Props.oddsub
