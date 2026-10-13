import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4b.deriv_diam_bound
import Submission.Work.WilG4b.volume_diam_bound

/-!
  Area G4b: the threshold measure bound.

  If `A ⊆ ℝ` is the fibre of an `Ω`-set of format `A₀` and degree `D` (i.e. its preimage
  under `x ↦ x 0` lies in `S.Ω A₀ D 1`) and `G : ℝ → ℝ` satisfies `a ≤ G t ≤ b` and
  `K < |deriv G t|` for all `t ∈ A`, then the Lebesgue measure of `A` is bounded by a
  constant (depending only on `S`, `A₀` and the degree) times `(b - a)/K`.

  The proof is the classical one-dimensional argument.  `S.comps` writes `A` as a union of
  at most `p.eval D` preconnected pieces.  On each piece `C`:
  * a preconnected subset of `ℝ` is order convex, so the points of the segment between two
    points of `C` lie in `C`, where `G` is differentiable (and hence continuous);
  * the mean value theorem applied on that segment produces a point where `|deriv G| > K`
    equals the secant slope, so distinct points of `C` are at distance at most
    `(b - a)/K`;
  * hence `C` sits inside an interval of length `2 * (b - a)/K`.
  Summing over the finitely many pieces (whose number is bounded) gives the claim.
-/

namespace Work.WilG4b

open WilkiesDesign

theorem thresh_measure_bound (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (A₀ : ℕ) (p₀ : Polynomial ℕ) :
    ∀ D : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K a b : ℝ) (G : ℝ → ℝ) (A : Set ℝ),
        0 < K → a ≤ b →
        {x : Fin 1 → ℝ | x 0 ∈ A} ∈ S.Ω A₀ (p₀.eval D) 1 →
        (∀ t ∈ A, a ≤ G t) →
        (∀ t ∈ A, G t ≤ b) →
        (∀ t ∈ A, K < |deriv G t|) →
        MeasureTheory.volume A ≤ ENNReal.ofReal (C * (b - a) / K) := by
  intro D
  obtain ⟨p, hp⟩ := S.comps A₀
  refine ⟨2 * ((p.eval (p₀.eval D) : ℕ) : ℝ), by positivity, ?_⟩
  intro K a b G A hK hab hX hGl hGu hGd
  -- The set of interest, as a subset of `ℝ¹`.
  let X : Set (Fin 1 → ℝ) := {x : Fin 1 → ℝ | x 0 ∈ A}
  have hXmem : X ∈ S.Ω A₀ (p₀.eval D) 1 := hX
  -- `S.comps` splits `X` into at most `p.eval D` preconnected pieces.
  obtain ⟨s, hcard, hconn, hsX⟩ := hp (p₀.eval D) X hXmem
  -- `A` is the image of `X` under the coordinate projection.
  have hA_eq : A = (fun x : Fin 1 → ℝ => x 0) '' X := by
    ext t
    constructor
    · intro ht
      exact ⟨fun _ => t, ht, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hA_un : A = ⋃ c ∈ s, (fun x : Fin 1 → ℝ => x 0) '' c := by
    rw [hA_eq, hsX]
    ext t
    simp only [Set.mem_image, Set.mem_sUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    tauto
  have hMnn : 0 ≤ (b - a) / K := div_nonneg (by linarith) hK.le
  -- Each piece has measure at most `2 * (b - a)/K`.
  have hcomp : ∀ c ∈ s, MeasureTheory.volume ((fun x : Fin 1 → ℝ => x 0) '' c) ≤
      ENNReal.ofReal (2 * ((b - a) / K)) := by
    intro c hc
    have hcX : c ⊆ X := by
      rw [hsX]
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.mpr hc)
    have himg : (fun x : Fin 1 → ℝ => x 0) '' c ⊆ A := by
      rw [hA_eq]
      exact Set.image_mono hcX
    have hconnc : IsPreconnected ((fun x : Fin 1 → ℝ => x 0) '' c) :=
      (hconn c hc).image _ (continuous_apply (0 : Fin 1)).continuousOn
    exact volume_diam_bound hMnn (deriv_diam_bound hK hconnc
      (fun t ht => hGl t (himg ht)) (fun t ht => hGu t (himg ht))
      (fun t ht => hGd t (himg ht)))
  -- Sum over the pieces and use the cardinality bound.
  calc MeasureTheory.volume A
      ≤ ∑ c ∈ s, MeasureTheory.volume ((fun x : Fin 1 → ℝ => x 0) '' c) := by
        rw [hA_un]
        exact MeasureTheory.measure_biUnion_finset_le s _
    _ ≤ ∑ c ∈ s, ENNReal.ofReal (2 * ((b - a) / K)) := Finset.sum_le_sum hcomp
    _ = (s.card : ENNReal) * ENNReal.ofReal (2 * ((b - a) / K)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((p.eval (p₀.eval D) : ℕ) : ENNReal) * ENNReal.ofReal (2 * ((b - a) / K)) :=
        mul_le_mul_left (by exact_mod_cast hcard) _
    _ = ENNReal.ofReal (((p.eval (p₀.eval D) : ℕ) : ℝ) * (2 * ((b - a) / K))) := by
        rw [← ENNReal.ofReal_natCast (p.eval (p₀.eval D)),
          ← ENNReal.ofReal_mul (p := ((p.eval (p₀.eval D) : ℕ) : ℝ))
            (q := 2 * ((b - a) / K)) (by positivity)]
    _ = ENNReal.ofReal ((2 * ((p.eval (p₀.eval D) : ℕ) : ℝ)) * (b - a) / K) := by
        congr 1
        ring

end Work.WilG4b
