import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.completion_of_sums
import Submission.Work.BMF.SD.corr_shift
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.SD.cell_aux
import Submission.Work.BMF.Free.large_sieve_poly
import Submission.Work.BMF.SD.class_pigeonhole_free
import Submission.Work.BMF.SD.polyrel_complete
import Submission.Work.BMF.SD.cell_len_bounds
import Submission.Work.BMF.SD.cell_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-!
## Copied ingredients (clash-free world)

`completion_phase` lives only in `Submission/Work/BMF/SD/scale_helpers.lean`, whose import closure
contains `SD/weyl_inverse` (and hence the `Work.BMF.SD.eC_mul_nat` that clashes with `SD/tk_short`).
Its statement and proof are copied here verbatim (as `completion_phase_cellpos`), together with the
auxiliary degree lemma `C_mul_X_sub_C_mem_degreeLE_cellpos`, whose ingredient
`C_mul_X_sub_C_pow_mem` is provided in the clash-free world as
`Work.BMF.FreeLS.C_mul_X_sub_C_pow_mem` (`Submission/Work/BMF/Free/large_sieve_poly.lean`).

The helper names carry a `_cellpos` suffix: the sibling file `SD/cell_center.lean` declares copies
of the same two helpers under the plain names `Work.BMF.SD.completion_phase` and
`Work.BMF.SD.C_mul_X_sub_C_mem_degreeLE`, and distinct names keep the two files jointly
importable. -/

/-- A degree-one polynomial of the shape `C θ * (X - C ζ)` has degree `≤ k` as soon as `k ≥ 1`.
(`Work.BMF.FreeLS.C_mul_X_sub_C_pow_mem` is the clash-free version of
`Work.BMF.C_mul_X_sub_C_pow_mem`, stated in `Submission/Work/BMF/Free/large_sieve_poly.lean`.)

The name carries the `_cellpos` suffix so that this file and `SD/cell_center.lean` -- which
contains a verbatim copy of the same two helpers under the plain names -- can be imported
together. -/
lemma C_mul_X_sub_C_mem_degreeLE_cellpos {k : ℕ} (hk : 1 ≤ k) (θ ζ : ℝ) :
    Polynomial.C θ * (Polynomial.X - Polynomial.C ζ) ∈ degreeLE ℝ (k : WithBot ℕ) := by
  simpa [pow_one] using Work.BMF.FreeLS.C_mul_X_sub_C_pow_mem k 1 hk θ ζ

/-- Completion of sums (MRT Lemma 2.4) upgraded to a statement about `corr`: a phase `P` that
correlates with `f` on the interval `[ζ, ζ+L]` of length `L` can be perturbed by a linear
polynomial `θ·(X - ζ)` vanishing at `ζ` so that the *full* interval `[ζ, ζ+L']` (with `L' ≍ L`)
carries a correlation of size `≫ L'`, the perturbation being uniformly bounded on `[ζ-4L', ζ+4L']`
by a constant depending only on `c` and `C₀`.

(Verbatim copy of `Work.BMF.completion_phase` of `SD/scale_helpers.lean`.) -/
theorem completion_phase_cellpos (k : ℕ) (hk : 1 ≤ k) (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 1 ≤ C₀) :
    ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (f : ℕ → ℂ) (P : ℝ[X]) (ζ L L' : ℝ), (∀ n, ‖f n‖ ≤ 1) →
      P ∈ degreeLE ℝ (k : WithBot ℕ) →
      1 ≤ ζ → 1 ≤ L' → 0 < L → L ≤ L' → L' ≤ C₀ * L → c * L ≤ ‖corr f P ζ L‖ →
      ∃ pol' : ℝ[X], pol' ∈ degreeLE ℝ (k : WithBot ℕ) ∧ c' * L' ≤ ‖corr f pol' ζ L'‖ ∧
        ∀ t : ℝ, |t - ζ| ≤ 4 * L' → |pol'.eval t - P.eval t| ≤ C := by
  obtain ⟨Cc, cc, hCc, hcc, hcomp⟩ := completion_of_sums
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set η : ℝ := min (c / C₀) 1 with hη
  have hηpos : 0 < η := lt_min (div_pos hc hC₀pos) one_pos
  have hηle1 : η ≤ 1 := min_le_right _ _
  have hηle : η ≤ c / C₀ := min_le_left _ _
  refine ⟨max (4 * Cc / η ^ 2) 1, cc * η ^ 4, lt_of_lt_of_le (by positivity) (le_max_right _ _),
    by positivity, ?_⟩
  intro f P ζ L L' hf hP hζ hL' hL hLL' hLC₀ hcorr
  have hηL' : η * L' ≤ c * L := by
    have h1 : η * L' ≤ (c / C₀) * L' := mul_le_mul_of_nonneg_right hηle (by linarith)
    have h2 : (c / C₀) * L' ≤ (c / C₀) * (C₀ * L) :=
      mul_le_mul_of_nonneg_left hLC₀ (by positivity)
    have h3 : (c / C₀) * (C₀ * L) = c * L := by field_simp
    linarith
  obtain ⟨θ, hθ, hsum⟩ := hcomp η hηpos hηle1 f hf P ζ (ζ + L) L' hL' hζ (by linarith) (by linarith)
    (le_trans hηL' hcorr)
  refine ⟨P + Polynomial.C θ * (Polynomial.X - Polynomial.C ζ), ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ hP (C_mul_X_sub_C_mem_degreeLE_cellpos hk θ ζ)
  · have hshift := corr_shift' f P ζ L' θ
    have hnorm : ‖corr f (P + Polynomial.C θ * (Polynomial.X - Polynomial.C ζ)) ζ L'‖
        = ‖corr f (P + Polynomial.C θ * Polynomial.X) ζ L'‖ := by
      rw [hshift, norm_mul, norm_eC, one_mul]
    have hsame : corr f (P + Polynomial.C θ * Polynomial.X) ζ L'
        = ∑ n ∈ natIcc ζ (ζ + L'), f n * eC (-((P + Polynomial.C θ * Polynomial.X).eval (n : ℝ))) := rfl
    rw [hnorm, hsame]
    exact hsum
  · intro t ht
    have hval : (P + Polynomial.C θ * (Polynomial.X - Polynomial.C ζ)).eval t - P.eval t
        = θ * (t - ζ) := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_X]
      ring
    have hθb : |θ| ≤ Cc / (η ^ 2 * L') := hθ
    have hη2L' : 0 < η ^ 2 * L' := by positivity
    have hb : |θ * (t - ζ)| ≤ 4 * Cc / η ^ 2 := by
      rw [abs_mul]
      have h1 : |θ| * |t - ζ| ≤ (Cc / (η ^ 2 * L')) * (4 * L') :=
        mul_le_mul hθb ht (abs_nonneg _) (by positivity)
      have h2 : (Cc / (η ^ 2 * L')) * (4 * L') = 4 * Cc / η ^ 2 := by
        field_simp
      linarith
    rw [hval]
    exact le_trans hb (le_max_left _ _)

/-- The cell step of scaling down, clash-free port of `Work.BMF.SD.cell_incidence`.

There are C, c, K > 0 such that for a 1-bounded f, a source phase function pol, and a nonempty
finite set S of pairs (y,p) -- p a prime with a <= p <= b and 5b <= 7a, positions y/p >= 1 all
within 3H/(2a) of a point x0 >= 1, each pair's rescaled phase p_*phi_y correlating with f at level
eta ON ITS OWN position y/p and of degree <= k (k >= 1) -- there are a point x', a polynomial pol'
of degree <= k and S' contained in S with #S' >= #S/(2K) such that
* x' IS the position of some pair of S (hence, in the intended use, an admissible point of the new
  family, since every pair of S has position >= X/(10a)),
* c*(H/a) <= ||corr f pol' x' (H/a)||,
* every q in S' satisfies |q.pos - x'| <= 3H/a and the PolyRel k C 1 relation
  (1/p)_*phi_y ~ pol' on [x', x' + H/a].

This is VERBATIM the statement of the proved `Work.BMF.SD.cell_incidence`, re-proved in the
clash-free import world so that the scaling-down assembly can use it together with SD/tk_bad_weight.
The reason a separate file is needed is purely syntactic: `SD/cell_incidence`'s import closure
contains `SD/weyl_inverse` (and `SD/scale_helpers` -> `Work.BMF.large_sieve_poly` ->
`SD/weyl_inverse`), whose `Work.BMF.SD.eC_mul_nat` clashes with `SD/tk_short`'s
(`environment already contains ...`).  The clash-free chain already exists:
`Submission.Work.BMF.SD.class_pigeonhole_free` (phase-class form of the polynomial large sieve,
proved, clash-free) replaces `SD/scale_helpers.large_sieve_rep`, and `completion_phase` (currently
only in `SD/scale_helpers.lean`) must be COPIED here, importing only its true dependencies
`Submission.Work.BMF.completion_of_sums`, `SD.corr_shift`, `polyrel_basic`, `SD.cell_aux`; nothing
else in `scale_helpers` is needed.

Hence the task is a port, not a new proof: copy `Submission/Work/BMF/SD/cell_incidence.lean`
(proved) and replace its two imported ingredients as described.  Note that the ball radius here is
3H/(2a) (as in `cell_incidence`), because the correlation hypothesis is stated at the pairs' own
positions; the radius must NOT be reduced, and no re-anchoring of the correlation to a centre is
possible (the two earlier reviews of `SD/cell_center.lean` gave spike-function counterexamples). -/
theorem cell_position (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∃ C c K : ℝ, 0 < C ∧ 0 < c ∧ 0 < K ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (pol : ℝ → Polynomial ℝ) (H a b x₀ : ℝ) (S : Finset (ℝ × ℕ)),
      0 < a → a ≤ b → 5 * b ≤ 7 * a → 1 ≤ H / a → 1 ≤ x₀ → 1 ≤ b → S.Nonempty →
      (∀ q ∈ S, 1 ≤ q.1 / (q.2 : ℝ)) →
      (∀ q ∈ S, a ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ b) →
      (∀ q ∈ S, |q.1 / (q.2 : ℝ) - x₀| ≤ 3 * H / (2 * a)) →
      (∀ q ∈ S, η * (H / (q.2 : ℝ)) ≤
        ‖Work.BMF.corr f (Work.BMF.dil (q.2 : ℝ) (pol q.1)) (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))‖) →
      (∀ q ∈ S,
        Work.BMF.dil (q.2 : ℝ) (pol q.1) ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
      ∃ (x' : ℝ) (pol' : Polynomial ℝ) (S' : Finset (ℝ × ℕ)),
        S' ⊆ S ∧ (∃ q ∈ S, x' = q.1 / (q.2 : ℝ)) ∧
        c * (H / a) ≤ ‖Work.BMF.corr f pol' x' (H / a)‖ ∧
        pol' ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) ∧
        ((S.card : ℝ) / (2 * K) ≤ (S'.card : ℝ)) ∧
        (∀ q ∈ S', |q.1 / (q.2 : ℝ) - x'| ≤ 3 * H / a ∧
          Work.BMF.PolyRel k C 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))
            (Work.BMF.dil (q.2 : ℝ) (pol q.1)) x' (H / a) pol') := by
  classical
  obtain ⟨C_ls, hC_ls_ge, K_ls, hK_ls_pos, hls⟩ := class_pigeonhole_free k η 2 hη (by norm_num)
  obtain ⟨C_c, c_c, hC_c_pos, hc_c_pos, hcomp⟩ := completion_phase_cellpos k hk η 2 hη (by norm_num)
  have hC_ls_pos : 0 < C_ls := by linarith
  refine ⟨max C_ls 2 * max C_ls 2 + max C_ls 2 + 1 + C_c, c_c, (K_ls : ℝ), ?_, hc_c_pos,
    ?_, ?_⟩
  · have h : (0 : ℝ) < max C_ls 2 := lt_of_lt_of_le hC_ls_pos (le_max_left _ _)
    nlinarith
  · exact_mod_cast hK_ls_pos
  intro f hf pol H a b x₀ S ha hab h5b hHa hx₀ hb hSne hpos hpcell hxcell hcorr hdeg
  -- The ambient length is positive.
  have hHpos : 0 < H := by
    have h1 : 1 * a ≤ H := (le_div_iff₀ ha).mp hHa
    linarith
  -- Enumerate `S` by `Fin S.card`.
  let eu : Fin S.card ≃ ↥S := (Finset.equivFin S).symm
  let e : Fin S.card → ℝ × ℕ := fun i => (eu i : ℝ × ℕ)
  have he_mem : ∀ i : Fin S.card, e i ∈ S := fun i => (eu i).2
  have he_inj : Function.Injective e := by
    intro i j hij
    exact eu.injective (Subtype.ext hij)
  let xs : Fin S.card → ℝ := fun i => (e i).1 / ((e i).2 : ℝ)
  let Ls : Fin S.card → ℝ := fun i => H / ((e i).2 : ℝ)
  let Ps : Fin S.card → ℝ[X] := fun i => dil ((e i).2 : ℝ) (pol (e i).1)
  have hpa : ∀ i : Fin S.card, a ≤ ((e i).2 : ℝ) := fun i => (hpcell (e i) (he_mem i)).1
  have hpb : ∀ i : Fin S.card, ((e i).2 : ℝ) ≤ b := fun i => (hpcell (e i) (he_mem i)).2
  -- Cell geometry for every index.
  have hlen : ∀ i : Fin S.card,
      0 < Ls i ∧ Ls i ≤ 2 * (H / a) ∧ (H / a) ≤ 2 * Ls i ∧
        |xs i - x₀| ≤ 2 * (H / a) := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5⟩ := cell_len_bounds hHpos ha h5b (hpa i) (hpb i)
    exact ⟨h1, h3, h4, le_trans (hxcell (e i) (he_mem i)) h5⟩
  -- The phase-class pigeonhole (clash-free form of the cell polynomial large sieve).
  have hN1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hUniv_ne : (Finset.univ : Finset (Fin S.card)).Nonempty :=
    ⟨⟨0, hN1⟩, Finset.mem_univ _⟩
  obtain ⟨A, hAsub, hAcard, i₀, hi₀A, hArel⟩ := hls S.card f x₀ (H / a) xs Ls Ps Finset.univ
    hUniv_ne hf hHa
    (fun i _ => hpos (e i) (he_mem i))
    (fun i _ => ⟨(hlen i).2.1, (hlen i).2.2.1, (hlen i).2.2.2⟩)
    (fun i _ => hdeg (e i) (he_mem i))
    (fun i _ => hcorr (e i) (he_mem i))
  -- Completion of sums at the representative pair.
  have hL₀ : 0 < Ls i₀ := (hlen i₀).1
  have hL₀L : Ls i₀ ≤ H / a := (cell_len_bounds hHpos ha h5b (hpa i₀) (hpb i₀)).2.1
  have hLa : 0 < H / a := div_pos hHpos ha
  have hL₀a : H / a ≤ 2 * Ls i₀ := (hlen i₀).2.2.1
  have hcorr₀ : η * Ls i₀ ≤ ‖corr f (Ps i₀) (xs i₀) (Ls i₀)‖ := hcorr (e i₀) (he_mem i₀)
  obtain ⟨pol', hpol'deg, hpol'corr, hpol'bd⟩ :=
    hcomp f (Ps i₀) (xs i₀) (Ls i₀) (H / a) hf (hdeg (e i₀) (he_mem i₀))
      (hpos (e i₀) (he_mem i₀)) hHa hL₀ hL₀L hL₀a hcorr₀
  -- The representative point and the subfamily of `PolyRel`-related pairs.
  let x' : ℝ := xs i₀
  let S' : Finset (ℝ × ℕ) := A.image e
  have hS'mem : ∀ q : ℝ × ℕ, q ∈ S' ↔ ∃ i ∈ A, e i = q := by
    intro q
    rw [show S' = A.image e from rfl, Finset.mem_image]
  refine ⟨x', pol', S', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `S' ⊆ S`
    intro q hq
    obtain ⟨i, _, he⟩ := (hS'mem q).mp hq
    rw [← he]
    exact he_mem i
  · -- `x'` is the position of a pair of `S`
    exact ⟨e i₀, he_mem i₀, rfl⟩
  · -- the completed correlation at the representative
    exact hpol'corr
  · -- the completed phase has degree `≤ k`
    exact hpol'deg
  · -- the cardinality bound
    have hcard : S'.card = A.card := by
      rw [show S' = A.image e from rfl]
      exact Finset.card_image_of_injective A he_inj
    rw [hcard]
    have hAn : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
    have hKposR : (0 : ℝ) < (K_ls : ℝ) := by exact_mod_cast hK_ls_pos
    have hAcard' : (S.card : ℝ) ≤ (A.card : ℝ) * (K_ls : ℝ) := by simpa using hAcard
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K_ls : ℝ))]
    nlinarith [hAcard', hAn, hKposR]
  · -- the per-pair incidence
    intro q hq
    obtain ⟨i, hiA, rfl⟩ := (hS'mem q).mp hq
    obtain ⟨l1, l2, l3, l4, l5⟩ := cell_len_bounds hHpos ha h5b (hpa i) (hpb i)
    obtain ⟨m1, m2, m3, m4, m5⟩ := cell_len_bounds hHpos ha h5b (hpa i₀) (hpb i₀)
    have hCm2 : (2 : ℝ) ≤ max C_ls 2 := le_max_right _ _
    have hCmL : C_ls ≤ max C_ls 2 := le_max_left _ _
    have hCmpos : 0 < max C_ls 2 := lt_of_lt_of_le hC_ls_pos hCmL
    constructor
    · -- distance to the representative
      exact (cell_ball ha hHpos (hpa i) (hxcell (e i) (he_mem i)) (hxcell (e i₀) (he_mem i₀))
        (t := xs i) (Set.mem_Icc.mpr ⟨le_rfl, by linarith [l1]⟩)).1
    · -- `PolyRel` with the completed phase
      have hb' : ∀ t ∈ Set.Icc (xs i) (xs i + Ls i),
          |pol'.eval t - (Ps i₀).eval t| ≤ C_c := by
        intro t ht
        exact hpol'bd t ((cell_ball ha hHpos (hpa i) (hxcell (e i) (he_mem i))
          (hxcell (e i₀) (he_mem i₀)) ht).2)
      have hR' : PolyRel k (max C_ls 2) 1 (xs i) (Ls i) (Ps i) (xs i₀) (Ls i₀) (Ps i₀) :=
        PolyRel.mono (hArel i hiA) hCmL l1.le m1.le
      have h1' : Ls i₀ ≤ max C_ls 2 * (H / a) := by nlinarith [m2, hLa.le, hCm2]
      have h2' : H / a ≤ max C_ls 2 * Ls i₀ := by nlinarith [m4, hCm2, m1]
      have h3' : |xs i₀ - x'| ≤ max C_ls 2 * Ls i₀ := by
        rw [show x' = xs i₀ from rfl, sub_self, abs_zero]
        nlinarith [hCm2, m1]
      exact polyrel_complete hR' hCmpos hC_c_pos.le l1 hLa h1' h2' h3'
        (Submodule.sub_mem _ hpol'deg (hdeg (e i₀) (he_mem i₀))) hb'

end Work.BMF.SD
