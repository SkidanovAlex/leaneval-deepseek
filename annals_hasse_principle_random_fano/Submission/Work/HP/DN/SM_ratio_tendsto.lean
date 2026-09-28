
import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.DN.realSol_iff
import Submission.Work.HP.DN.SM_padic_periodic
import Submission.Work.HP.DN.realSolCone_facts_alt
import Submission.Work.HP.DN.cone_periodic_prim_limit
import Submission.Work.HP.DN.primCount_lower
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.tau_basic

/-! (D6) `SM_ratio_tendsto`: for each fixed `M` the ratio of `SM M` converges.

Route (design review hasse2, §2.2 D6): apply D4 `cone_periodic_prim_limit` twice, once with
`K = realSolCone d n` and `P` the `p`-adic part of `SM` (periodic with period `QM M`, D5'), and
once with `K = Set.univ`, `P = True` for the denominator; `primCount_lower` (a general-range
version of `count_basic`) shows that the denominator's limit is positive, so the ratio of the two
convergent sequences converges.
-/

namespace Work.HP.DN

open Filter Finset MeasureTheory Pointwise
open Work.HP

/-! ## Small helper facts -/

/-- The Euclidean sphere in `ι → ℝ` (in the `Work.HP.rNorm` norm) is null. -/
lemma volume_rNorm_sphere {ι : Type*} [Fintype ι] [Nonempty ι] :
    volume {t : ι → ℝ | rNorm t = 1} = 0 := by
  have hset : {t : ι → ℝ | rNorm t = 1}
      = WithLp.toLp 2 ⁻¹' (Metric.sphere (0 : EuclideanSpace ℝ ι) 1) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere, rNorm_eq_normE,
      dist_eq_norm, sub_zero]
  rw [hset]
  rw [(PiLp.volume_preserving_toLp ι).measure_preimage
      Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
  exact MeasureTheory.Measure.addHaar_sphere (μ := MeasureTheory.volume)
    (0 : EuclideanSpace ℝ ι) 1

/-- `rNorm` is continuous. -/
lemma continuous_rNorm {ι : Type*} [Fintype ι] : Continuous (fun t : ι → ℝ => rNorm t) := by
  have h : (fun t : ι → ℝ => rNorm t)
      = (fun t : ι → ℝ => ‖(WithLp.toLp 2 t : EuclideanSpace ℝ ι)‖) := by
    funext t; exact rNorm_eq_normE t
  rw [h]
  exact continuous_norm.comp (PiLp.continuous_toLp 2 fun _ : ι => ℝ)

/-- The frontier of the Euclidean unit ball is contained in the unit sphere. -/
lemma frontier_unitBallR_subset {ι : Type*} [Fintype ι] :
    frontier (unitBallR ι) ⊆ {t : ι → ℝ | rNorm t = 1} := by
  intro t ht
  simp only [Set.mem_setOf_eq]
  by_contra hne
  have hcont := continuous_rNorm (ι := ι)
  rw [frontier_eq_inter_compl_interior] at ht
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hopen : IsOpen {t : ι → ℝ | rNorm t < 1} := isOpen_lt hcont continuous_const
    have hsub : {t : ι → ℝ | rNorm t < 1} ⊆ unitBallR ι :=
      fun y hy => show rNorm y ≤ 1 from le_of_lt hy
    have hmem : t ∈ interior (unitBallR ι) := (interior_maximal hsub hopen) hlt
    exact ht.1 hmem
  · have hopen : IsOpen {t : ι → ℝ | 1 < rNorm t} := isOpen_lt continuous_const hcont
    have hsub : {t : ι → ℝ | 1 < rNorm t} ⊆ (unitBallR ι)ᶜ := by
      intro y hy hy'
      have hy1 : 1 < rNorm y := hy
      have hy2 : rNorm y ≤ 1 := hy'
      exact absurd hy2 (not_le.mpr hy1)
    have hmem : t ∈ interior ((unitBallR ι)ᶜ) := (interior_maximal hsub hopen) hgt
    exact ht.2 hmem

/-- `volume (frontier (univ ∩ unitBallR ι)) = 0`. -/
lemma volume_frontier_univ_unitBallR {ι : Type*} [Fintype ι] [Nonempty ι] :
    volume (frontier ((Set.univ : Set (ι → ℝ)) ∩ unitBallR ι)) = 0 := by
  rw [Set.univ_inter]
  exact measure_mono_null frontier_unitBallR_subset (volume_rNorm_sphere (ι := ι))

/-- `Q_M ≥ 1`. -/
lemma one_le_QM (M : ℕ) : 1 ≤ QM M := by
  rw [QM]
  refine Finset.one_le_prod₀ fun p hp => ?_
  exact one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr (Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2))

/-- `Mon d n` has at least two elements. -/
lemma two_le_NN (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 2 ≤ NN d n := by
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hne : monDiHP d n i0 ≠ monDiHP d n i1 := by
    intro h
    have hc := congrArg (fun m : Mon d n => ((m.1 i0 : Fin (d + 1)) : ℕ)) h
    have e1 : ((monDiHP d n i0).1 i0 : ℕ) = d := by
      change (if i0 = i0 then d else 0) = d
      rw [if_pos rfl]
    have e2 : ((monDiHP d n i1).1 i0 : ℕ) = 0 := by
      change (if i0 = i1 then d else 0) = 0
      rw [if_neg h01]
    rw [e1, e2] at hc
    omega
  haveI : Nontrivial (Mon d n) := ⟨monDiHP d n i0, monDiHP d n i1, hne⟩
  exact Fintype.one_lt_card

/-! ## The main theorem -/

/-- (D6) For each fixed `M` the ratio of `SM M` converges (D2, D4 twice, D5', `primCount_lower`). -/
theorem SM_ratio_tendsto (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (M : ℕ) :
    ∃ L : ℝ, Tendsto (fun A : ℝ => ratio d n A (SM d n M)) atTop (nhds L) := by
  have hcard : 2 ≤ Fintype.card (Mon d n) := two_le_NN d n (by omega) (by omega)
  haveI : Nonempty (Mon d n) := Fintype.card_pos_iff.mp (by omega)
  -- the cone facts (D2)
  obtain ⟨hKc, hKsc, hKfr⟩ := realSolCone_facts_alt d n hd (by omega : 1 ≤ n)
  -- D4 with the real-solubility cone and the `p`-adic predicate
  obtain ⟨L1, hL1⟩ := cone_periodic_prim_limit (ι := Mon d n) hcard (realSolCone d n) hKc hKsc hKfr
    (QM M) (one_le_QM M) (fun a => ∀ p : ℕ, p.Prime → p ≤ M → PrimModZero d n a p (4 * M))
    (fun a b => SM_padic_periodic d n M a b)
  -- D4 with everything (the denominator)
  obtain ⟨L2, hL2⟩ := cone_periodic_prim_limit (ι := Mon d n) hcard Set.univ isClosed_univ
    (fun s t _ => by simp) (volume_frontier_univ_unitBallR (ι := Mon d n)) 1 le_rfl
    (fun _ => True) (fun a b => by simp)
  -- identify the two counted sets with `primSet`
  have hset1 : ∀ A : ℝ, ({a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ realSolCone d n ∧
      ∀ p : ℕ, p.Prime → p ≤ M → PrimModZero d n a p (4 * M)} : Set (Mon d n → ℤ))
      = primSet d n A (SM d n M) := by
    intro A
    ext a
    simp only [Set.mem_setOf_eq, primSet, SM]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, (realSol_iff d n a).mpr h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, (realSol_iff d n a).mp h3, h4⟩
  have hset2 : ∀ A : ℝ, ({a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧
      toR a ∈ (Set.univ : Set (Mon d n → ℝ)) ∧ True} : Set (Mon d n → ℤ))
      = primSet d n A (fun _ => True) := by
    intro A
    ext a
    simp [primSet]
  have hnum : Tendsto (fun A : ℝ => primCount d n A (SM d n M) / A ^ NN d n) atTop (nhds L1) := by
    refine hL1.congr' ?_
    filter_upwards with A
    have h : primCount d n A (SM d n M)
        = (({a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ realSolCone d n ∧
            ∀ p : ℕ, p.Prime → p ≤ M → PrimModZero d n a p (4 * M)}.ncard : ℕ) : ℝ) := by
      rw [primCount, hset1 A]
    rw [h]
  have hden : Tendsto (fun A : ℝ => primCount d n A (fun _ => True) / A ^ NN d n) atTop (nhds L2) := by
    refine hL2.congr' ?_
    filter_upwards with A
    have h : primCount d n A (fun _ => True)
        = (({a : Mon d n → ℤ | IsPrim a ∧ eNorm a ≤ A ∧
            toR a ∈ (Set.univ : Set (Mon d n → ℝ)) ∧ True}.ncard : ℕ) : ℝ) := by
      rw [primCount, hset2 A]
    rw [h]
  -- the denominator's limit is positive
  obtain ⟨c, hcpos, hc⟩ := primCount_lower d n hd hn
  have hL2pos : 0 < L2 := by
    refine lt_of_lt_of_le hcpos (le_of_tendsto_of_tendsto tendsto_const_nhds hden ?_)
    filter_upwards [hc, eventually_gt_atTop (0:ℝ)] with A hA hA0
    rw [le_div_iff₀ (pow_pos hA0 _)]
    exact hA
  -- assemble
  refine ⟨L1 / L2, ?_⟩
  have hden_ne : ∀ᶠ A in atTop, primCount d n A (fun _ => True) / A ^ NN d n ≠ 0 := by
    filter_upwards [hden.eventually (isOpen_Ioi.mem_nhds hL2pos)] with A hA
    exact ne_of_gt hA
  refine (Tendsto.div hnum hden hL2pos.ne').congr' ?_
  filter_upwards [eventually_ne_atTop (0:ℝ)] with A hA0
  have hA : (A : ℝ) ^ NN d n ≠ 0 := pow_ne_zero _ hA0
  simp only [Pi.div_apply, ratio]
  field_simp

end Work.HP.DN
