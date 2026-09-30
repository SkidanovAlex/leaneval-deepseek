import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.completion_of_sums
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

/-- A degree-one polynomial of the shape `C θ * (X - C ζ)` has degree `≤ k` as soon as `k ≥ 1`. -/
lemma C_mul_X_sub_C_mem_degreeLE {k : ℕ} (hk : 1 ≤ k) (θ ζ : ℝ) :
    Polynomial.C θ * (Polynomial.X - Polynomial.C ζ) ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) := by
  simpa [pow_one] using Work.BMF.FreeLS.C_mul_X_sub_C_pow_mem k 1 hk θ ζ

/-- Completion of sums (MRT Lemma 2.4) upgraded to a statement about `corr`: a phase `P` that
correlates with `f` on the interval `[ζ, ζ+L]` of length `L` can be perturbed by a linear
polynomial `θ·(X - ζ)` vanishing at `ζ` so that the *full* interval `[ζ, ζ+L']` (with `L' ≍ L`)
carries a correlation of size `≫ L'`, the perturbation being uniformly bounded on `[ζ-4L', ζ+4L']`
by a constant depending only on `c` and `C₀`.

This is a verbatim copy of `Work.BMF.completion_phase` (`SD/scale_helpers.lean`) in the
clash-free import world: it imports only `Submission.Work.BMF.completion_of_sums`, `SD.corr_shift`
(via `SD.polyrel_complete`) and `SD.cell_aux`, so that it can be used together with
`Submission.Work.BMF.SD.tk_short`. -/
theorem completion_phase (k : ℕ) (hk : 1 ≤ k) (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 1 ≤ C₀) :
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
  · exact Submodule.add_mem _ hP (C_mul_X_sub_C_mem_degreeLE hk θ ζ)
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

/-- The cell step of scaling down, anchored at the cell centre, in the clash-free world.

There are C, c, K > 0 such that for a 1-bounded f, a source phase function pol and a nonempty
finite set S of pairs (y,p) -- p a prime with a <= p <= b and 5b <= 7a, positions y/p >= 1 all
within H/a of a point x0 >= 1, each pair's rescaled phase p_*phi_y correlating with f at level eta
AT THE CENTRE x0 on the interval of length H/p, and of degree <= k (k >= 1) -- there are pol' of
degree <= k and S' contained in S with #S' >= #S/(2K) such that c*(H/a) <= ||corr f pol' x0 (H/a)||
and every q in S' satisfies both |q.pos - x0| <= 3H/a and the PolyRel k C 1 relation
(1/p)_*phi_y ~ pol' on [x0, x0 + H/a].

This is the variant of the proved Work.BMF.SD.cell_incidence that the scaling-down assembly needs:
the family point is the centre x0, which the caller chooses >= X/(10a) (hence admissible for the
new family), rather than the representative pair's position; and the ball radius is H/a, so the
distance 3H/a required by the target's incPairs clause is met by every member of S'.  The existing
cell_incidence anchors its correlation bound at the representative's position x'; a correlation at
a pair's own position can NOT be moved to a centre H/a away, hence the hypothesis below is stated
at x0, exactly as in cell_incidence with x0 in place of x'.  (In the assembly the pairs are counted
as good at their OWN positions, and the centre-anchored hypothesis is obtained from that by the
elementary transfer 'the two index sets differ by at most 2|x - x0| + 2 elements', with a ball
radius rho small compared with eta*H/a.)

Its proof is cell_incidence's, on the clash-free chain: Work.BMF.SD.class_pigeonhole_free
(phase-class/covering form of the polynomial large sieve) is applied with the family point x0 as
the common position of every pair -- the hypotheses of the cover are then exactly the ones of the
statement (the correlation of the pair's rescaled phase at x0 on the interval of length H/p, and
the trivial geometry |x0 - x0| <= 2*H/a) -- selecting a representative i0 related to >= #S/K of the
pairs.  completion_phase (copied above out of SD/scale_helpers.lean, importing only its true
dependencies) completes the representative's correlated pair to [x0, x0 + H/a]; the relation, which
so far has BOTH intervals anchored at x0, is re-anchored to the pair's own position by
Work.BMF.PolyRel.symm + Work.BMF.PolyRel.change_second' + Work.BMF.PolyRel.symm (the displacement
H/a, and the resulting need to re-bound the `ε`-slot on the shifted interval, being absorbed by the
constant via `poly_growth` inside `PolyRel.symm`), and finally Work.BMF.SD.polyrel_complete moves
the second interval to [x0, x0 + H/a] and substitutes the completed phase pol' for the
representative's phase, the extra displacement being absorbed by the constant. -/
theorem cell_center (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∃ C c K : ℝ, 0 < C ∧ 0 < c ∧ 0 < K ∧
      ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (pol : ℝ → Polynomial ℝ) (H a b x₀ : ℝ) (S : Finset (ℝ × ℕ)),
      0 < a → a ≤ b → 5 * b ≤ 7 * a → 1 ≤ H / a → 1 ≤ x₀ → 1 ≤ b → S.Nonempty →
      (∀ q ∈ S, 1 ≤ q.1 / (q.2 : ℝ)) →
      (∀ q ∈ S, a ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ b) →
      (∀ q ∈ S, |q.1 / (q.2 : ℝ) - x₀| ≤ H / a) →
      (∀ q ∈ S, η * (H / (q.2 : ℝ)) ≤
        ‖Work.BMF.corr f (Work.BMF.dil (q.2 : ℝ) (pol q.1)) x₀ (H / (q.2 : ℝ))‖) →
      (∀ q ∈ S,
        Work.BMF.dil (q.2 : ℝ) (pol q.1) ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
      ∃ (pol' : Polynomial ℝ) (S' : Finset (ℝ × ℕ)),
        S' ⊆ S ∧
        c * (H / a) ≤ ‖Work.BMF.corr f pol' x₀ (H / a)‖ ∧
        pol' ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) ∧
        ((S.card : ℝ) / (2 * K) ≤ (S'.card : ℝ)) ∧
        (∀ q ∈ S', |q.1 / (q.2 : ℝ) - x₀| ≤ 3 * H / a ∧
          Work.BMF.PolyRel k C 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ))
            (Work.BMF.dil (q.2 : ℝ) (pol q.1)) x₀ (H / a) pol') := by
  classical
  obtain ⟨C_ls, hC_ls_ge, K_ls, hK_ls_pos, hcp⟩ := class_pigeonhole_free k η 2 hη (by norm_num)
  have hC_ls_pos : 0 < C_ls := lt_of_lt_of_le (by norm_num) hC_ls_ge
  obtain ⟨C_c, c_c, hC_c_pos, hc_c_pos, hcomp⟩ := completion_phase k hk η 2 hη (by norm_num)
  refine ⟨symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) *
            symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) +
          symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) + 1 + C_c,
        c_c, (K_ls : ℝ), ?_, hc_c_pos, ?_, ?_⟩
  · have hC1p : 0 < symmConst k C_ls := symmConst_pos hC_ls_pos
    have hXp : 0 < symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1 := by
      have := mul_pos hC1p hC1p; linarith
    have h : 0 < symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) :=
      symmConst_pos hXp
    have hh : 0 < symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) *
        symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) := mul_pos h h
    linarith [hh, h, hC_c_pos]
  · exact_mod_cast hK_ls_pos
  intro f hf pol H a b x₀ S ha hab h5b hHa hx₀ hb hSne hpos hpcell hxcell hcorr hdeg
  have hHpos : 0 < H := by
    have h1 : 1 * a ≤ H := (le_div_iff₀ ha).mp hHa
    linarith
  have hHdiv : 0 < H / a := div_pos hHpos ha
  have hHdivnn : 0 ≤ H / a := hHdiv.le
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
  have hLpos : ∀ i : Fin S.card, 0 < Ls i :=
    fun i => (cell_len_bounds hHpos ha h5b (hpa i) (hpb i)).1
  have hLle : ∀ i : Fin S.card, Ls i ≤ H / a :=
    fun i => (cell_len_bounds hHpos ha h5b (hpa i) (hpb i)).2.1
  have hLge : ∀ i : Fin S.card, H / a ≤ 2 * Ls i :=
    fun i => (cell_len_bounds hHpos ha h5b (hpa i) (hpb i)).2.2.2.1
  -- The phase-class pigeonhole, with `x₀` as the common position of every pair.
  obtain ⟨A, _hAsub, hAcard, i₀, hi₀A, hArel⟩ :=
    hcp S.card f x₀ (H / a) (fun _ => x₀) Ls Ps Finset.univ
      ⟨⟨0, Finset.card_pos.mpr hSne⟩, Finset.mem_univ _⟩ hf hHa
      (fun _ _ => hx₀)
      (fun i _ => ⟨by linarith [hLle i, hHdivnn], hLge i, by
        simp only [sub_self, abs_zero]; exact mul_nonneg (by norm_num) hHdivnn⟩)
      (fun i _ => hdeg (e i) (he_mem i))
      (fun i _ => hcorr (e i) (he_mem i))
  -- Completion of sums for the representative's correlated pair.
  have hcorr₀ : η * Ls i₀ ≤ ‖corr f (Ps i₀) x₀ (Ls i₀)‖ := hcorr (e i₀) (he_mem i₀)
  obtain ⟨pol', hpol'deg, hpol'corr, hpol'bd⟩ :=
    hcomp f (Ps i₀) x₀ (Ls i₀) (H / a) hf (hdeg (e i₀) (he_mem i₀)) hx₀ hHa
      (hLpos i₀) (hLle i₀) (hLge i₀) hcorr₀
  refine ⟨pol', A.image e, ?_, hpol'corr, hpol'deg, ?_, ?_⟩
  · -- `S' ⊆ S`
    intro q hq
    obtain ⟨i, _, hei⟩ := Finset.mem_image.mp hq
    rw [← hei]
    exact he_mem i
  · -- the cardinality bound
    have hcard : (A.image e).card = A.card := Finset.card_image_of_injective _ he_inj
    rw [hcard]
    have hKpos : (0 : ℝ) < (K_ls : ℝ) := by exact_mod_cast hK_ls_pos
    have h1 : (S.card : ℝ) ≤ (A.card : ℝ) * (K_ls : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin] at hAcard
      exact hAcard
    have h2 : (S.card : ℝ) / (2 * (K_ls : ℝ)) ≤ (S.card : ℝ) / (K_ls : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hKpos (by linarith)
    have h3 : (S.card : ℝ) / (K_ls : ℝ) ≤ (A.card : ℝ) := by
      rw [div_le_iff₀ hKpos]
      linarith
    linarith
  · -- the per-pair incidence
    intro q hq
    obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨l1, l2, l3, l4, l5⟩ := cell_len_bounds hHpos ha h5b (hpa i) (hpb i)
    obtain ⟨m1, m2, m3, m4, m5⟩ := cell_len_bounds hHpos ha h5b (hpa i₀) (hpb i₀)
    have hC1pos : 0 < symmConst k C_ls := symmConst_pos hC_ls_pos
    have hC1ge1 : 1 ≤ symmConst k C_ls := by
      have h := symmConst_ge_self (k := k) hC_ls_pos
      linarith
    have hC1ge2 : 2 ≤ symmConst k C_ls := by
      have h := symmConst_ge_self (k := k) hC_ls_pos
      linarith
    have hXpos : 0 < symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1 := by positivity
    have hXge1 : 1 ≤ symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1 := by
      nlinarith [sq_nonneg (symmConst k C_ls), hC1pos]
    have hXge2 : 2 ≤ symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1 := by
      nlinarith [hC1ge2]
    have hCbge1 : 1 ≤ symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) :=
      le_trans hXge1 (symmConst_ge_self (k := k) hXpos)
    have hCbge2 : 2 ≤ symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) :=
      le_trans hXge2 (symmConst_ge_self (k := k) hXpos)
    have hCbpos : 0 < symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) :=
      symmConst_pos hXpos
    -- (1) symmetry: the relation with the second interval at the pair's position.
    have hsym1 : PolyRel k (symmConst k C_ls) 1 x₀ (Ls i₀) (Ps i₀) x₀ (Ls i) (Ps i) :=
      PolyRel.symm (hArel i hiA) hC_ls_pos (hLpos i) (hLpos i₀)
    -- (2) move the second interval to the pair's own position (phase unchanged).
    have h3s : |x₀ - xs i| ≤ symmConst k C_ls * Ls i := by
      have hx : |x₀ - xs i| ≤ H / a := by
        rw [abs_sub_comm]; exact hxcell (e i) (he_mem i)
      calc |x₀ - xs i| ≤ H / a := hx
        _ ≤ 2 * Ls i := l4
        _ ≤ symmConst k C_ls * Ls i := mul_le_mul_of_nonneg_right hC1ge2 (hLpos i).le
    have hshift := PolyRel.change_second' (η := (0 : ℝ[X])) (Cη := 0) hsym1 hC1pos le_rfl
      (hLpos i₀) (hLpos i) (hLpos i)
      (by nlinarith [hC1ge1, hLpos i]) (by nlinarith [hC1ge1, hLpos i]) h3s
      (Submodule.zero_mem _) (fun t _ => by simp)
    have hsym2 : PolyRel k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) 1
        x₀ (Ls i₀) (Ps i₀) (xs i) (Ls i) (Ps i) := by
      simpa using hshift
    -- (3) symmetry again: the first interval is now the pair's own position.
    have hsym3 : PolyRel k (symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1))
        1 (xs i) (Ls i) (Ps i) x₀ (Ls i₀) (Ps i₀) :=
      PolyRel.symm hsym2 hXpos (hLpos i₀) (hLpos i)
    -- (4) complete the second interval to `[x₀, x₀ + H/a]` with the completed phase `pol'`.
    have hb' : ∀ t ∈ Set.Icc (xs i) (xs i + Ls i),
        |pol'.eval t - (Ps i₀).eval t| ≤ C_c := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have hti : |t - xs i| ≤ Ls i := by
        rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htx : |t - x₀| ≤ 4 * (H / a) := by
        calc |t - x₀| ≤ |t - xs i| + |xs i - x₀| := by
              rw [show t - x₀ = (t - xs i) + (xs i - x₀) by ring]
              exact abs_add_le _ _
          _ ≤ Ls i + H / a := add_le_add hti (hxcell (e i) (he_mem i))
          _ ≤ H / a + H / a := by linarith [hLle i]
          _ = 2 * (H / a) := by ring
          _ ≤ 4 * (H / a) := by linarith [hHdivnn]
      exact hpol'bd t htx
    have hdeg_diff : pol' - Ps i₀ ∈ degreeLE ℝ (k : WithBot ℕ) :=
      Submodule.sub_mem _ hpol'deg (hdeg (e i₀) (he_mem i₀))
    refine ⟨?_, ?_⟩
    · -- distance to the centre
      calc |(e i).1 / ((e i).2 : ℝ) - x₀| ≤ H / a := hxcell (e i) (he_mem i)
        _ ≤ 3 * H / a := by
            rw [show 3 * H / a = 3 * (H / a) by ring]
            exact le_mul_of_one_le_left hHdivnn (by norm_num)
    · -- the `PolyRel` incidence
      have h1'' : Ls i₀ ≤
          symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) * (H / a) :=
        calc Ls i₀ ≤ H / a := m2
          _ = 1 * (H / a) := by ring
          _ ≤ symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) * (H / a) :=
              mul_le_mul_of_nonneg_right hCbge1 hHdivnn
      have h2'' : H / a ≤
          symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) * Ls i₀ :=
        calc H / a ≤ 2 * Ls i₀ := m4
          _ ≤ symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) * Ls i₀ :=
              mul_le_mul_of_nonneg_right hCbge2 m1.le
      have h3'' : |x₀ - x₀| ≤
          symmConst k (symmConst k C_ls * symmConst k C_ls + symmConst k C_ls + 1) * Ls i₀ := by
        rw [sub_self, abs_zero]
        exact mul_nonneg hCbpos.le m1.le
      exact polyrel_complete hsym3 hCbpos hC_c_pos.le (hLpos i) hHdiv h1'' h2'' h3''
        hdeg_diff hb'

end Work.BMF.SD
