import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.JPrelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators
open scoped ComplexConjugate

/-! ## Elementary facts about the characters, the truncation and the pairing

The proof of `STruncR_selfadjoint` expands both truncations as finite sums of characters
(`STruncR_eq_sum`) and integrates term by term.  The only analytic input is that a *bounded* factor
(`trunc ρ ε c m · e_m`, respectively the character itself) can be pulled out of the integral, which
is what the two lemmas `integral_re_mul_char` and `integral_mul_re_char` record; the remaining
numerical identity `Re (a · conj b) = Re (b · conj a)` is `re_mul_star_comm`. -/

/-- The character `fourierExp m` has unit modulus. -/
lemma fourierExp_norm_eq_one {ι : Type*} [Fintype ι] (m : ι → ℤ) (z : ι → ℝ) :
    ‖Work.Diff.STE.fourierExp m z‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((m i : ℤ) : ℂ) * (z i : ℂ))
      = (((2 * Real.pi * ∑ i, ((m i : ℤ) : ℝ) * z i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Work.Diff.STE.fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

/-- The character `fourierExp m` is continuous. -/
lemma continuous_fourierExp_gen {ι : Type*} [Fintype ι] (m : ι → ℤ) :
    Continuous (Work.Diff.STE.fourierExp m) := by
  unfold Work.Diff.STE.fourierExp
  fun_prop

/-- Real part of a complex number times a real number. -/
lemma re_mul_ofReal' (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- `Re (a · conj b) = Re (b · conj a)`: symmetry of the real part of a Hermitian pairing. -/
lemma re_mul_star_comm (a b : ℂ) : (a * star b).re = (b * star a).re := by
  rw [← Complex.conj_re (a * star b)]
  simp
  ring

/-- The truncated multiplier is real, so the previous symmetry survives multiplication by
`ρ (ε • m)`. -/
lemma re_ofReal_mul_star_swap (r : ℝ) (a b : ℂ) :
    ((r : ℂ) * a * star b).re = ((r : ℂ) * b * star a).re := by
  rw [mul_assoc, mul_assoc, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_mul_star_comm]

/-- **Integrability of `c · e_m · h`.**  A bounded (continuous) factor times the coercion of an
integrable real function is integrable. -/
lemma integrableOn_char_mul {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    {h : (ι → ℝ) → ℝ} (hh : IntegrableOn h s) (m : ι → ℤ) (c : ℂ) :
    IntegrableOn (fun z => c * Work.Diff.STE.fourierExp m z * (h z : ℂ)) s := by
  refine Integrable.mono' (g := fun z => ‖c‖ * ‖h z‖) ?_ ?_ ?_
  · exact hh.norm.const_mul ‖c‖
  · exact (Continuous.aestronglyMeasurable
        (continuous_const.mul (continuous_fourierExp_gen m))).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable)
  · filter_upwards with z
    rw [norm_mul, norm_mul, fourierExp_norm_eq_one, mul_one]
    simp

/-- **Term-by-term integration of `Re (c · e_m) · h`**: the complex factor is constant and the
character is bounded, so
`∫ (c · e_m).re · h = Re (c · ∫ e_m · h)`. -/
lemma integral_re_mul_char {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    {h : (ι → ℝ) → ℝ} (hh : IntegrableOn h s) (m : ι → ℤ) (c : ℂ) :
    ∫ z in s, (c * Work.Diff.STE.fourierExp m z).re * h z
      = (c * ∫ z in s, Work.Diff.STE.fourierExp m z * (h z : ℂ)).re := by
  have hpt : ∀ z : ι → ℝ, (c * Work.Diff.STE.fourierExp m z).re * h z
      = (c * Work.Diff.STE.fourierExp m z * (h z : ℂ)).re :=
    fun z => (re_mul_ofReal' _ _).symm
  have hint := integrableOn_char_mul (s := s) hh m c
  calc ∫ z in s, (c * Work.Diff.STE.fourierExp m z).re * h z
      = ∫ z in s, (c * Work.Diff.STE.fourierExp m z * (h z : ℂ)).re :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z in s, c * Work.Diff.STE.fourierExp m z * (h z : ℂ)).re := integral_re hint
    _ = (c * ∫ z in s, Work.Diff.STE.fourierExp m z * (h z : ℂ)).re := by
        have hconst : (∫ z in s, c * Work.Diff.STE.fourierExp m z * (h z : ℂ))
            = c * ∫ z in s, Work.Diff.STE.fourierExp m z * (h z : ℂ) := by
          rw [show (fun z : ι → ℝ => c * Work.Diff.STE.fourierExp m z * (h z : ℂ))
              = (fun z => c * (Work.Diff.STE.fourierExp m z * (h z : ℂ))) from
            funext fun z => mul_assoc _ _ _]
          exact MeasureTheory.integral_const_mul c _
        rw [hconst]

/-- The same term-by-term integration with the factors interchanged (this is the shape needed for
the right-hand side of the self-adjointness). -/
lemma integral_mul_re_char {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    {h : (ι → ℝ) → ℝ} (hh : IntegrableOn h s) (m : ι → ℤ) (c : ℂ) :
    ∫ z in s, h z * (c * Work.Diff.STE.fourierExp m z).re
      = (c * ∫ z in s, Work.Diff.STE.fourierExp m z * (h z : ℂ)).re := by
  rw [show (∫ z in s, h z * (c * Work.Diff.STE.fourierExp m z).re)
        = ∫ z in s, (c * Work.Diff.STE.fourierExp m z).re * h z from
      integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)]
  exact integral_re_mul_char hh m c

/-- **The Friedrichs truncation `STruncR ρ ε` is self-adjoint for the unweighted `L²` pairing of
the centred cube `(-1/2,1/2]^n`.**  For real `f`, `g` supported in the open cube and integrable on
the centred cube,

  `∫_{cube} (STruncR ρ ε f) · g = ∫_{cube} f · (STruncR ρ ε g)`,

where `STruncR ρ ε h` is the (real part of the) Fourier series whose coefficients are
`ρ (ε • m) · perCoeff h m`, i.e. a Fourier multiplier with the *real* multiplier `ρ (ε • ·)`.

Proof route (the two hypotheses `hperf`, `hperg` are exactly
`Diff/STE/B3/fourierCoeff_periodization` instantiated at `f` and `g`): by
`Work.Diff.STE.B3.STruncR_eq_sum` both sides are finite sums over the box
`truncBox (n := Module.finrank ℝ E) ε`; integrate term by term (each character is bounded and
`g` resp. `f` is integrable on the cube).  The `m`-th term of the left-hand side is
`Re (trunc ρ ε (perCoeff f) m · ∫_{cube} e_m · g)` `= ρ (ε•m) · Re (perCoeff f m · conj (perCoeff g m))`
(use `hperg (-m)` to identify `∫_{cube} e_m g` with `perCoeff g (-m)` and
`Work.Diff.STE.B3.star_fourierCoeff_per` to replace it by the conjugate of `perCoeff g m`), and the
`m`-th term of the right-hand side is the same expression (which is symmetric in `f`, `g` because
`Re (z) = Re (conj z)`). -/
theorem STruncR_selfadjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (f g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf_supp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hg_supp : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hf_int : MeasureTheory.IntegrableOn f
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume)
    (hg_int : MeasureTheory.IntegrableOn g
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume)
    (hperf : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
      Work.Diff.STE.B3.perCoeff f m
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            Work.Diff.STE.fourierExp (-m) z * ((f z : ℝ) : ℂ))
    (hperg : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
      Work.Diff.STE.B3.perCoeff g m
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            Work.Diff.STE.fourierExp (-m) z * ((g z : ℝ) : ℂ)) :
    (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        Work.Diff.STE.B3Data.STruncR ρ ε f z * g z)
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          f z * Work.Diff.STE.B3Data.STruncR ρ ε g z := by
  classical
  have hFeq : ∀ z, Work.Diff.STE.B3Data.STruncR ρ ε f z
      = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
            * Work.Diff.STE.fourierExp m z).re :=
    fun z => Work.Diff.STE.B3.STruncR_eq_sum ρ ε hε hρ0 f z
  have hGeq : ∀ z, Work.Diff.STE.B3Data.STruncR ρ ε g z
      = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m
            * Work.Diff.STE.fourierExp m z).re :=
    fun z => Work.Diff.STE.B3.STruncR_eq_sum ρ ε hε hρ0 g z
  -- The left-hand side is the sum over the box of `Re (trunc ρ ε (perCoeff f) m · conj ĉ_g m)`.
  have hL : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        Work.Diff.STE.B3Data.STruncR ρ ε f z * g z)
      = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
            * star (Work.Diff.STE.B3.perCoeff g m)).re := by
    have h1 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.B3Data.STruncR ρ ε f z * g z)
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
                * Work.Diff.STE.fourierExp m z).re) * g z :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hFeq z])
    rw [h1]
    have h2 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
              * Work.Diff.STE.fourierExp m z).re) * g z)
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
                * Work.Diff.STE.fourierExp m z).re * g z :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => Finset.sum_mul _ _ _)
    rw [h2]
    have hswap : ∀ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
        Integrable (fun z => (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
              * Work.Diff.STE.fourierExp m z).re * g z)
          (MeasureTheory.volume.restrict (Work.Diff.STE.B3Data.centreCube (E := E))) := by
      intro m hm
      have hint := integrableOn_char_mul (s := Work.Diff.STE.B3Data.centreCube (E := E))
        hg_int m (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m)
      exact hint.re.congr (Filter.Eventually.of_forall fun z => re_mul_ofReal' _ _)
    rw [MeasureTheory.integral_finsetSum
      (Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε) hswap]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [integral_re_mul_char (s := Work.Diff.STE.B3Data.centreCube (E := E)) (h := g) hg_int m
      (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m)]
    have hinner : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp m z * (g z : ℂ)) = star (Work.Diff.STE.B3.perCoeff g m) := by
      have hstar : star (Work.Diff.STE.B3.perCoeff g m) = Work.Diff.STE.B3.perCoeff g (-m) :=
        Work.Diff.STE.B3.star_fourierCoeff_per (n := Module.finrank ℝ E) g m
      rw [hstar, hperg (-m), neg_neg]
    rw [hinner]
  -- The right-hand side is the sum over the box of the same expression (symmetric in `f`, `g`).
  have hR : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        f z * Work.Diff.STE.B3Data.STruncR ρ ε g z)
      = ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff f) m
            * star (Work.Diff.STE.B3.perCoeff g m)).re := by
    have h1 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          f z * Work.Diff.STE.B3Data.STruncR ρ ε g z)
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            f z * (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m
                * Work.Diff.STE.fourierExp m z).re) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hGeq z])
    rw [h1]
    have h2 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          f z * (∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m
                * Work.Diff.STE.fourierExp m z).re))
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            ∑ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
              f z * (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m
                * Work.Diff.STE.fourierExp m z).re :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => Finset.mul_sum _ _ _)
    rw [h2]
    have hswap : ∀ m ∈ Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε,
        Integrable (fun z => f z * (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m
              * Work.Diff.STE.fourierExp m z).re)
          (MeasureTheory.volume.restrict (Work.Diff.STE.B3Data.centreCube (E := E))) := by
      intro m hm
      have hint := integrableOn_char_mul (s := Work.Diff.STE.B3Data.centreCube (E := E))
        hf_int m (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m)
      exact hint.re.congr (Filter.Eventually.of_forall fun z =>
        (re_mul_ofReal' _ _).trans (mul_comm _ _))
    rw [MeasureTheory.integral_finsetSum
      (Work.Diff.STE.B3.truncBox (n := Module.finrank ℝ E) ε) hswap]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [integral_mul_re_char (s := Work.Diff.STE.B3Data.centreCube (E := E)) (h := f) hf_int m
      (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeff g) m)]
    have hinner : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp m z * (f z : ℂ)) = star (Work.Diff.STE.B3.perCoeff f m) := by
      have hstar : star (Work.Diff.STE.B3.perCoeff f m) = Work.Diff.STE.B3.perCoeff f (-m) :=
        Work.Diff.STE.B3.star_fourierCoeff_per (n := Module.finrank ℝ E) f m
      rw [hstar, hperf (-m), neg_neg]
    rw [hinner]
    simp only [Work.Diff.STE.trunc]
    exact re_ofReal_mul_star_swap _ _ _
  rw [hL, hR]

end Work.Diff.STE.B3
