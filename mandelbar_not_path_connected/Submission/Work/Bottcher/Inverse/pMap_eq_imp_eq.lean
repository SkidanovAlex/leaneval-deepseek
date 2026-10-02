import Mathlib
import Submission.Work.Bottcher.Inverse.BottcherReflect

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of a Böttcher coordinate with the antiholomorphic functional equation

Let `φ` be a function on the escaping set `{G_c > 0}` of the tricorn map `T_c(z) = z̄² + c`
which is

* *odd* (`φ(-z) = -φ z`),
* satisfies the antiholomorphic Böttcher equation `φ (T_c z) = conj (φ z)²`,
* and is nowhere vanishing.

Then two escaping points with the same `p_c = T_c ∘ T_c`-image *and* the same `φ`-value coincide.

The two possibilities `p_c u = p_c v` opens besides `u = v` are

* `v = -u`: ruled out by oddness, which would force `φ u = -φ u = 0`;
* `u² + v² + 2 conj c = 0`: equivalent to `T_c u = -T_c v`; conjugating the
  functional equation at `u` and `v` together with `φ u = φ v` gives
  `φ (T_c u) = φ (T_c v)`, while oddness at `T_c u` gives `φ (T_c v) = -φ (T_c u)`,
  again forcing `φ (T_c u) = 0`.

The factorisation `p_c u - p_c v = (u-v)(u+v)(u²+v²+2 conj c)` is `pMap_sub_pMap`.
-/

namespace Work.Bottcher.Inverse

open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

theorem pMap_eq_imp_eq (c : ℂ) (φ : ℂ → ℂ)
    (hodd : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (-z) = -φ z)
    (hT : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (LeanEval.ComplexAnalysis.Tantibar c z) = (starRingEnd ℂ) (φ z) ^ 2)
    (hZne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → φ z ≠ 0)
    {u v : ℂ} (hu : 0 < Work.Bottcher.green c u) (hv : 0 < Work.Bottcher.green c v)
    (hp : Work.Bottcher.pMap c u = Work.Bottcher.pMap c v) (hφ : φ u = φ v) : u = v := by
  -- `a = -a` forces `a = 0`.
  have key : ∀ a : ℂ, a = -a → a = 0 := by
    intro a ha
    have h : a + a = 0 := (eq_neg_iff_add_eq_zero).mp ha
    have h2 : (2 : ℂ) * a = 0 := by rw [two_mul]; exact h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  -- The quartic factorisation of the difference.
  have hfac : (u - v) * (u + v) * (u ^ 2 + v ^ 2 + 2 * (starRingEnd ℂ) c) = 0 := by
    have h := pMap_sub_pMap c u v
    rw [hp, sub_self] at h
    exact h.symm
  rcases mul_eq_zero.mp hfac with h12 | h3
  · rcases mul_eq_zero.mp h12 with huv | huv
    · exact sub_eq_zero.mp huv
    · -- `u + v = 0`, i.e. `v = -u`, is incompatible with oddness.
      have hv_eq : v = -u := eq_neg_of_add_eq_zero_right huv
      have hphi_neg : φ u = -φ u := by
        have h1 : φ u = φ (-u) := by rw [← hv_eq, hφ]
        exact h1.trans (hodd u hu)
      exact absurd (key (φ u) hphi_neg) (hZne u hu)
  · -- `u² + v² + 2 conj c = 0`, i.e. `T_c u = -T_c v`.
    have hTuv : Tantibar c u + Tantibar c v = 0 := by
      have hc : (starRingEnd ℂ) u ^ 2 + (starRingEnd ℂ) v ^ 2 + 2 * c = 0 := by
        have h := congrArg (starRingEnd ℂ) h3
        simp only [map_add, map_mul, map_pow, map_ofNat, map_zero, starRingEnd_self_apply] at h
        exact h
      simp only [LeanEval.ComplexAnalysis.Tantibar]
      linear_combination hc
    have hTv : Tantibar c v = -Tantibar c u := eq_neg_of_add_eq_zero_right hTuv
    -- `T_c u` is escaping.
    have hgreenT : 0 < Work.Bottcher.green c (Tantibar c u) := by
      rw [Work.Bottcher.Green.green_pos_iff]
      have hu' := (Work.Bottcher.Green.green_pos_iff c u).mp hu
      have hshift : ∀ n : ℕ, (Tantibar c)^[n] (Tantibar c u) = (Tantibar c)^[n+1] u :=
        fun n => (Function.iterate_succ_apply (Tantibar c) n u).symm
      have hcomp : Tendsto (fun a : ℕ => ‖(Tantibar c)^[a+1] u‖) atTop atTop :=
        hu'.comp (tendsto_add_atTop_nat 1)
      simpa only [hshift] using hcomp
    have hphiT_eq : φ (Tantibar c u) = φ (Tantibar c v) := by
      rw [hT u hu, hT v hv, hφ]
    have hphiT_neg : φ (Tantibar c v) = -φ (Tantibar c u) := by
      rw [hTv]; exact hodd (Tantibar c u) hgreenT
    have hphi_neg : φ (Tantibar c u) = -φ (Tantibar c u) := hphiT_eq.trans hphiT_neg
    exact absurd (key (φ (Tantibar c u)) hphi_neg) (hZne (Tantibar c u) hgreenT)

end Work.Bottcher.Inverse
