import Mathlib
import Submission.Work.WilE9G.Sard.volume_image_univ_eq_zero_of_lt
import Submission.Work.WilE9G.Sard.volume_image_eq_zero_of_flat_along_vec
import Submission.Work.WilE9G.Sard.rankPosReductionAux
import Submission.Work.WilE9G.Sard.morseDecomposition

/-!
# Morse–Sard for `C^{d-n+1}` maps `ℝ^d → ℝ^n`

The target statement (kept verbatim at the end of this file) is the classical sharp Morse–Sard
theorem: for `f : ℝ^d → ℝ^n` of class `C^k` with `k ≥ max 1 (d-n+1)`, the set of critical values
`f '' {x | ¬ Surjective (fderiv ℝ f x)}` is Lebesgue-null.

## What is proved in this file

* `det_eq_zero_of_not_surjective`, `morseSard_square`, `morseSard_of_le`: the cases `d = n` and
  `n ≥ d` (for `d < n` every point is critical and the image is null by
  `volume_image_univ_eq_zero_of_lt`; for `d = n` the statement is the square case of Sard, which is
  Mathlib's `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).
* `volume_image_posRank_eq_zero`: the positive-rank part.  The set of critical points at which
  `fderiv ℝ f x ≠ 0` is covered by the countably many balls supplied by `rankPosReduction`
  (Lindelöf's theorem, i.e. second countability of `ℝ^d`, makes the cover countable); each of these
  balls has null image by the induction hypothesis in dimension `d - 1` with target dimension
  `n - 1`, where the required smoothness `(d-1)-(n-1)+1 = d-n+1` is exactly `k`.
* `volume_image_rankZero_eq_zero`: the rank-zero part, i.e. the image of `{x | fderiv ℝ f x = 0}`.
  This is Sard's rank-zero theorem (Sard 1942, Theorem 6.1), derived from the Morse/Norton
  decomposition `morseDecomposition` together with the covering engine
  `volume_image_eq_zero_of_flat_along_vec`: the decomposition covers the rank-zero critical set by
  countably many bounded sets on each of which `f` is flat of order `q`, and the engine kills the
  image of each piece as soon as `d ≤ q·n`.
* `morseSard_of_rankZero` and `morseSard`: the assembly.  `Crit f = {fderiv ≠ 0} ∪ {fderiv = 0}`
  and both parts have null image, the positive-rank one by strong induction on `d`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.WilE9G.Sard

open MeasureTheory Metric

/-- For a continuous linear endomorphism of `ℝ^n`, non-surjectivity forces the determinant to
vanish (the converse direction is `LinearMap.range_lt_top_of_det_eq_zero`). -/
theorem det_eq_zero_of_not_surjective {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hA : ¬ Function.Surjective A) : A.det = 0 := by
  by_contra h
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    by_contra hk
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot (f := A.toLinearMap)).mpr hk)
  have hinj : Function.Injective A.toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A.toLinearMap :=
    LinearMap.injective_iff_surjective.mp hinj
  exact hA fun y => hsurj y

/-- **Morse–Sard, the square case `d = n`.**  This is the `d = n` instance of Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`. -/
theorem morseSard_square {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ 1 f) :
    MeasureTheory.volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := MeasureTheory.volume) (f := f) (f' := fun x => fderiv ℝ f x)
    (s := {x : Fin n → ℝ | ¬ Function.Surjective (fderiv ℝ f x)}) ?_ ?_
  · intro x _
    exact (hf.differentiable_one x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact det_eq_zero_of_not_surjective (fderiv ℝ f x) hx

/-- **Morse–Sard, the case `n ≥ d`.** -/
theorem morseSard_of_le {d n : ℕ} (hn : d ≤ n) (f : (Fin d → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ (max 1 (d - n + 1)) f) :
    MeasureTheory.volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  rcases Nat.lt_or_eq_of_le hn with hlt | heq
  · -- `d < n`: the critical set is everything, and a differentiable image of `ℝ^d` is null.
    refine measure_mono_null ?_ (volume_image_univ_eq_zero_of_lt hlt f (hf.of_le (le_max_left _ _)))
    exact Set.image_mono (Set.subset_univ _)
  · -- `d = n`: the square case of Sard.
    subst heq
    exact morseSard_square f (hf.of_le (le_max_left _ _))

/-- **Rank-zero case of Sard's theorem** (Sard 1942, Theorem 6.1): the image of the set of
critical points of rank zero under a `C^q` map is null as soon as `q * n ≥ d`.

Proof: the Morse/Norton decomposition of the rank-zero critical set (A. P. Morse 1939, Sard 1942
Theorem 5.1), imported above as `morseDecomposition`, covers `{Df = 0}` by countably many bounded
sets on each of which `f` is flat of order `q`; the covering engine
`volume_image_eq_zero_of_flat_along_vec` kills the image of each piece, and a countable union of
null sets is null. -/
theorem volume_image_rankZero_eq_zero {d n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (hqn : d ≤ q * n)
    (f : (Fin d → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ q f)
    (E : Set (Fin d → ℝ)) (hE : E ⊆ {x | fderiv ℝ f x = 0}) :
    volume (f '' E) = 0 := by
  obtain ⟨A', hbdd, hcov, hflat⟩ := morseDecomposition hn hq f hf E hE
  have hpiece : ∀ j, volume (f '' A' j) = 0 := fun j =>
    volume_image_eq_zero_of_flat_along_vec hn hqn f (A' j) (hbdd j) (hflat j)
  have himg : f '' E ⊆ ⋃ j, f '' A' j := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨j, ⟨x, hj, rfl⟩⟩
  refine le_antisymm ?_ bot_le
  calc volume (f '' E) ≤ volume (⋃ j, f '' A' j) := measure_mono himg
    _ = 0 := measure_iUnion_null hpiece
/-- **Positive-rank part**: if the theorem is known in dimension `d - 1` and target dimension
`n - 1` at the same smoothness `k`, then the critical values of the positive-rank part of `f` are
null.  The local input is `rankPosReduction`; the passage from local to global is Lindelöf's
theorem (second countability of `ℝ^d`). -/
theorem volume_image_posRank_eq_zero {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (f : (Fin d → ℝ) → (Fin n → ℝ)) (hf : ContDiff ℝ k f) (hk : 1 ≤ k)
    (IH : ∀ g : (Fin (d - 1) → ℝ) → (Fin (n - 1) → ℝ), ContDiff ℝ k g →
      volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0) :
    volume (f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ {x | fderiv ℝ f x ≠ 0})) = 0 := by
  classical
  set C : Set (Fin d → ℝ) := {x | ¬ Function.Surjective (fderiv ℝ f x)} with hC
  set S : Set (Fin d → ℝ) := {x | fderiv ℝ f x ≠ 0} with hS
  have hpt : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ volume (f '' (C ∩ Metric.ball x r)) = 0 :=
    fun x hx => rankPosReductionAux hd hn f hf hk x hx IH
  have hchoose : ∀ x : Fin d → ℝ, ∃ r : ℝ, 0 < r ∧
      (x ∈ S → volume (f '' (C ∩ Metric.ball x r)) = 0) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨r, hr, hnull⟩ := hpt x hx
      exact ⟨r, hr, fun _ => hnull⟩
    · exact ⟨1, one_pos, fun hx' => absurd hx' hx⟩
  choose r hrpos hrnull using hchoose
  have hLind : IsLindelof S := HereditarilyLindelofSpace.isLindelof S
  obtain ⟨t, htc, htS, hcov⟩ := hLind.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x _ => Metric.ball_mem_nhds x (hrpos x))
  haveI : Countable {x // x ∈ t} := htc
  have hsub : f '' (C ∩ S) ⊆ ⋃ x : {x // x ∈ t}, f '' (C ∩ Metric.ball x.1 (r x.1)) := by
    rintro y ⟨z, ⟨hzC, hzS⟩, rfl⟩
    obtain ⟨x, hxt, hxz⟩ := Set.mem_iUnion₂.mp (hcov hzS)
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, ⟨z, ⟨hzC, hxz⟩, rfl⟩⟩
  refine le_antisymm ?_ bot_le
  calc volume (f '' (C ∩ S))
      ≤ volume (⋃ x : {x // x ∈ t}, f '' (C ∩ Metric.ball x.1 (r x.1))) := measure_mono hsub
    _ = 0 := measure_iUnion_null (fun x => hrnull x.1 (htS x.1 x.2))
/-- **The sharp Morse–Sard theorem**, assembled from a rank-zero input.  Strong induction on the
source dimension `d`: the critical set splits into the rank-zero part (the input `hrz`) and the
positive-rank part (handled by `rankPosReduction` plus second countability, the induction
hypothesis being the instance in dimension `d - 1` with target dimension `n - 1`, where the
required smoothness `(d-1)-(n-1)+1` coincides with `d - n + 1`). -/
theorem morseSard_of_rankZero
    (hrz : ∀ ⦃d n k : ℕ⦄, 1 ≤ n → 2 ≤ k → d ≤ k * n → ∀ (f : (Fin d → ℝ) → (Fin n → ℝ)),
      ContDiff ℝ k f → volume (f '' {x : Fin d → ℝ | fderiv ℝ f x = 0}) = 0) :
    ∀ d : ℕ, ∀ (n : ℕ) (f : (Fin d → ℝ) → (Fin n → ℝ)),
    ContDiff ℝ (max 1 (d - n + 1)) f →
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d IH =>
    intro n f hf
    by_cases hnd : d ≤ n
    · exact morseSard_of_le hnd f hf
    · push_neg at hnd
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0
        have hempty : {x : Fin d → ℝ | ¬ Function.Surjective (fderiv ℝ f x)} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
          intro y
          exact ⟨0, Subsingleton.elim _ y⟩
        rw [hempty, Set.image_empty, measure_empty]
      · have hd : 1 ≤ d := by omega
        have hk1 : 1 ≤ d - n + 1 := by omega
        have hkmax : (max 1 ((d : WithTop ℕ∞) - n + 1)) = (((d - n + 1 : ℕ)) : WithTop ℕ∞) := by
          rw [show ((d : WithTop ℕ∞) - n) = (((d - n : ℕ)) : WithTop ℕ∞) from rfl]
          rw [show (((d - n : ℕ)) : WithTop ℕ∞) + 1
              = (((d - n + 1 : ℕ)) : WithTop ℕ∞) from by push_cast; ring]
          exact max_eq_right (by exact_mod_cast hk1)
        have hf' : ContDiff ℝ (d - n + 1) f := by
          rw [hkmax] at hf
          exact hf
        have hIH : ∀ g : (Fin (d - 1) → ℝ) → (Fin (n - 1) → ℝ), ContDiff ℝ (d - n + 1) g →
            volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0 := by
          intro g hg
          have h3 : (d - 1) - (n - 1) + 1 = d - n + 1 := by omega
          have hmax' : (max 1 (((d - 1 : ℕ) : WithTop ℕ∞) - ((n - 1 : ℕ)) + 1))
              = (((d - n + 1 : ℕ)) : WithTop ℕ∞) := by
            rw [show (((d - 1 : ℕ) : WithTop ℕ∞) - ((n - 1 : ℕ)))
                = ((((d - 1) - (n - 1) : ℕ)) : WithTop ℕ∞) from rfl]
            rw [show ((((d - 1) - (n - 1) : ℕ)) : WithTop ℕ∞) + 1
                = ((((d - 1) - (n - 1) + 1 : ℕ)) : WithTop ℕ∞) from by push_cast; ring]
            rw [h3]
            exact max_eq_right (by exact_mod_cast hk1)
          exact IH (d - 1) (by omega) (n - 1) g (by rw [hmax']; exact hg)
        have hpos := volume_image_posRank_eq_zero hd hn f hf' hk1 hIH
        have hdle : d ≤ (d - n + 1) * n := by
          have h1 : d = (d - n) + n := (Nat.sub_add_cancel (le_of_lt hnd)).symm
          have h2 : (d - n + 1) * n = (d - n) * n + n := by ring
          have h3 : d - n ≤ (d - n) * n := by
            cases n with
            | zero => omega
            | succ m => exact Nat.le_mul_of_pos_right (m := m + 1) (d - (m + 1)) (by omega)
          omega
        have hzero : volume (f '' {x : Fin d → ℝ | fderiv ℝ f x = 0}) = 0 :=
          hrz hn (by omega) hdle f hf'
        set C : Set (Fin d → ℝ) := {x | ¬ Function.Surjective (fderiv ℝ f x)} with hC
        set Z : Set (Fin d → ℝ) := {x | fderiv ℝ f x = 0} with hZ
        have hsplit : C ⊆ Z ∪ (C ∩ {x | fderiv ℝ f x ≠ 0}) := by
          intro x hx
          by_cases h : fderiv ℝ f x = 0
          · exact Or.inl h
          · exact Or.inr ⟨hx, h⟩
        have hpos' : volume (f '' (C ∩ {x | fderiv ℝ f x ≠ 0})) = 0 := by
          rw [hC] at hpos
          exact hpos
        refine le_antisymm ?_ bot_le
        calc volume (f '' C)
            ≤ volume (f '' (Z ∪ (C ∩ {x | fderiv ℝ f x ≠ 0}))) :=
              measure_mono (Set.image_mono hsplit)
          _ = volume (f '' Z ∪ f '' (C ∩ {x | fderiv ℝ f x ≠ 0})) := by rw [Set.image_union]
          _ ≤ volume (f '' Z) + volume (f '' (C ∩ {x | fderiv ℝ f x ≠ 0})) :=
              measure_union_le _ _
          _ = 0 := by rw [hZ, hpos', hzero]; simp
/-- **The sharp Morse–Sard theorem.**  For `d ≤ n` this is `morseSard_of_le`.  For `d > n` write
`k = d - n + 1`; the critical set splits into the positive-rank part (a countable union of balls, on
each of which `rankPosReduction` and the induction hypothesis in dimension `d - 1` give nullity) and
the rank-zero part `{x | fderiv ℝ f x = 0}`, whose image is null by
`volume_image_rankZero_eq_zero` with `q = k` (Morse/Norton decomposition plus the covering
engine). -/
theorem morseSard {d n : ℕ} (f : (Fin d → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ (max 1 (d - n + 1)) f) :
    MeasureTheory.volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  morseSard_of_rankZero (fun {d n k} hn _ hkn f hf' =>
    volume_image_rankZero_eq_zero hn (by omega) hkn f hf' _ (fun x hx => hx)) d n f hf

end Work.WilE9G.Sard
