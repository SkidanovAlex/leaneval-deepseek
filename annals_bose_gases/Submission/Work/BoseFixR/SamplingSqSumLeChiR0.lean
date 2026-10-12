import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.SamplingSqSumLeChiR0`

`Σ_{k : Lab N} (chat W (kmomLab ℓ N k))² ≤ ℓ³ (2χ+1)³ B ∫W`.

The proof periodises `W` over the lattice `ℓℤ³`,

    P(y) = Σ_{n ∈ ℤ³} W(y + ℓn)   (a finite sum on the fundamental domain `cell ℓ`),

whose number of non-zero terms at a point `y ∈ cell ℓ` is at most `(2χ+1)³` (`card_le_of_norm_le`:
every coordinate of `n` must lie in an interval of length `2χ`).  Hence `0 ≤ P ≤ (2χ+1)³ B` on
`cell ℓ`, and `∫_{cell ℓ} P² ≤ (2χ+1)³ B ∫_{cell ℓ} P`.  The tiling identity
`∫_{ℝ³} f = Σ_n ∫_{cell ℓ} f(· + ℓn)` identifies `∫_{cell ℓ} P = ∫ W` and the Fourier coefficients
`∫_{cell ℓ} P e^{-i⟪q,·⟫} = Ŵ(q)` (the lattice phase `e^{-i⟪q,ℓn⟫} = 1`, `exp_inner_kmomLab_lat`).
Bessel for the orthogonal family `1_{cell ℓ} e^{i⟪kmomLab ℓ N k,·⟫}` (weight `ℓ³`,
`bessel_sum_integral`) then gives the claim.
-/

noncomputable section

set_option maxHeartbeats 4000000

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter Metric

namespace Work.BoseFixR

/-! ## 1. Volume of the two boxes and integrability transfer -/

lemma measurableSet_cellI (ℓ : ℝ) : MeasurableSet (cellI ℓ) := by
  have h : cellI ℓ = ⋂ i : Fin 3,
      {y : EuclideanSpace ℝ (Fin 3) | y i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2)} := by
    ext y; simp [cellI, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable

lemma volume_cellI (ℓ : ℝ) : volume (cellI ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  let C : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ : Fin 3 => Set.Ico (-(ℓ / 2)) (ℓ / 2)
  have hcell : cellI ℓ =
      (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹' C := by
    ext y
    simp only [cellI, Set.mem_ofPred_eq, Set.mem_preimage, C, Set.mem_pi, Set.mem_univ,
      true_implies]
  have hCpi : C = (Set.univ : Set (Fin 3)).pi
      (fun _ : Fin 3 => (Set.Ico (-(ℓ / 2)) (ℓ / 2) : Set ℝ)) := by
    ext f
    simp only [C, Set.mem_pi, Set.mem_univ, true_implies]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)
  rw [hcell, MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hCmeas.nullMeasurableSet]
  rw [hCpi, MeasureTheory.volume_pi,
    MeasureTheory.Measure.pi_pi (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (s := fun _ : Fin 3 => (Set.Ico (-(ℓ / 2)) (ℓ / 2) : Set ℝ))]
  simp only [Real.volume_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ℓ / 2 - -(ℓ / 2) = ℓ by ring]
  rcases lt_or_ge 0 ℓ with h | h
  · exact (ENNReal.ofReal_pow (le_of_lt h) 3).symm
  · rw [ENNReal.ofReal_eq_zero.mpr h, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
      ENNReal.ofReal_eq_zero.mpr (by nlinarith [sq_nonneg ℓ])]

lemma volume_cellI_ne_top (ℓ : ℝ) : volume (cellI ℓ) ≠ ⊤ := by
  rw [volume_cellI ℓ]; exact ENNReal.ofReal_ne_top

lemma volume_cell_sdiff_cellI (ℓ : ℝ) : volume (cell ℓ \ cellI ℓ) = 0 := by
  have hsub : cellI ℓ ⊆ cell ℓ := cellI_subset_cell ℓ
  have hne : volume (cellI ℓ) ≠ ⊤ := volume_cellI_ne_top ℓ
  rw [MeasureTheory.measure_sdiff hsub (measurableSet_cellI ℓ).nullMeasurableSet hne,
    cell_eq_boxL, volume_boxL, volume_cellI, tsub_self]

/-- The half-open box is a.e. the closed box. -/
lemma cellI_ae_eq_cell (ℓ : ℝ) : (cellI ℓ : Set (EuclideanSpace ℝ (Fin 3))) =ᵐ[volume] cell ℓ := by
  have hnull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      x ∉ cell ℓ \ cellI ℓ := by
    rw [MeasureTheory.ae_iff]
    convert volume_cell_sdiff_cellI ℓ using 2
    ext a; simp [Set.mem_sdiff, and_comm]
  filter_upwards [hnull] with x hx
  apply propext
  constructor
  · exact fun h => cellI_subset_cell ℓ h
  · intro hxc
    by_contra hxi
    exact hx ⟨hxc, hxi⟩

/-- An integral over the half-open box equals the integral over the closed box. -/
lemma setIntegral_cellI_eq_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → E) :
    ∫ x in cellI ℓ, g x = ∫ x in cell ℓ, g x :=
  MeasureTheory.setIntegral_congr_set (cellI_ae_eq_cell ℓ)

/-! ## 2. The relevant lattice labels and the counting bound -/

/-- The lattice labels `n ∈ ℤ³` that can contribute to the periodisation on the box `cell ℓ`. -/
def latBox (χ : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(⌈χ + 1 / 2⌉)) ⌈χ + 1 / 2⌉)

lemma mem_latBox {χ : ℝ} {n : Fin 3 → ℤ} :
    n ∈ latBox χ ↔ ∀ i, |n i| ≤ (⌈χ + 1 / 2⌉ : ℤ) := by
  rw [latBox, Fintype.mem_piFinset]
  exact forall_congr' fun i => by rw [Finset.mem_Icc, abs_le]

/-- Off the box `latBox χ` the periodised summand vanishes. -/
lemma eq_zero_of_notMem_latBox {ℓ R χ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * χ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {n : Fin 3 → ℤ} (hn : n ∉ latBox χ) {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ cell ℓ) :
    W (y + lat ℓ n) = 0 := by
  by_contra hne
  have hmem : y + lat ℓ n ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hne)
  have hball : ‖y + lat ℓ n‖ < R := by
    have h := hsupp hmem
    rwa [Metric.mem_ball, dist_zero_right] at h
  apply hn
  rw [mem_latBox]
  intro i
  have hyi : |y i| ≤ ℓ / 2 := hy i
  have h2 : |y i + ℓ * (n i : ℝ)| ≤ ℓ * χ := by
    calc |y i + ℓ * (n i : ℝ)| = |(y + lat ℓ n) i| := by simp
      _ ≤ ‖y + lat ℓ n‖ := by simpa using PiLp.norm_apply_le (y + lat ℓ n) i
      _ ≤ ℓ * χ := le_trans (le_of_lt hball) hRℓ
  have key : ℓ * (|n i| : ℝ) ≤ ℓ * (χ + 1 / 2) := by
    calc ℓ * (|n i| : ℝ) = |ℓ * (n i : ℝ)| := by rw [abs_mul, abs_of_pos hℓ]
      _ = |(y i + ℓ * (n i : ℝ)) - y i| := by
            rw [show (y i + ℓ * (n i : ℝ)) - y i = ℓ * (n i : ℝ) by ring]
      _ ≤ |y i + ℓ * (n i : ℝ)| + |y i| := by
            simpa using abs_sub_le (y i + ℓ * (n i : ℝ)) 0 (y i)
      _ ≤ ℓ * χ + ℓ / 2 := add_le_add h2 hyi
      _ = ℓ * (χ + 1 / 2) := by ring
  have key2 : (|n i| : ℝ) ≤ (ℓ * (χ + 1 / 2)) / ℓ :=
    (le_div_iff₀ hℓ).mpr (by rw [mul_comm]; exact key)
  have hdiv : (ℓ * (χ + 1 / 2)) / ℓ = χ + 1 / 2 := mul_div_cancel_left₀ _ (ne_of_gt hℓ)
  rw [hdiv] at key2
  have h4 : (|n i| : ℝ) ≤ ((⌈χ + 1 / 2⌉ : ℤ) : ℝ) := le_trans key2 (Int.le_ceil _)
  exact_mod_cast h4

/-- **The lattice counting bound.**  A finite set of lattice labels `n` whose translates `y + ℓn`
all lie in the ball of radius `R ≤ ℓχ` has at most `(2χ+1)³` elements: each coordinate of `n`
lies in an interval of length `2χ`. -/
theorem card_le_of_norm_le {ℓ R χ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * χ) (hχ : 0 ≤ χ)
    {y : EuclideanSpace ℝ (Fin 3)} (S : Finset (Fin 3 → ℤ))
    (hS : ∀ n ∈ S, ‖y + lat ℓ n‖ ≤ R) : (S.card : ℝ) ≤ (2 * χ + 1) ^ 3 := by
  classical
  have hcoord : ∀ (i : Fin 3) (n : Fin 3 → ℤ), n ∈ S →
      |((n i : ℤ) : ℝ) + y i / ℓ| ≤ χ := by
    intro i n hn
    have h1 : |(y + lat ℓ n) i| ≤ R :=
      le_trans (by simpa using PiLp.norm_apply_le (y + lat ℓ n) i) (hS n hn)
    have h2 : |y i + ℓ * (n i : ℝ)| ≤ ℓ * χ := by
      calc |y i + ℓ * (n i : ℝ)| = |(y + lat ℓ n) i| := by simp
        _ ≤ R := h1
        _ ≤ ℓ * χ := hRℓ
    have heq : ((n i : ℤ) : ℝ) + y i / ℓ = (y i + ℓ * (n i : ℝ)) / ℓ := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
    linarith
  set T : (i : Fin 3) → Finset ℤ := fun i => S.image (fun n => n i) with hTdef
  have hsub : S ⊆ Fintype.piFinset T := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hn
  have hTcard : ∀ i : Fin 3, ((T i).card : ℝ) ≤ 2 * χ + 1 := by
    intro i
    have hTi : T i ⊆ Finset.Icc ⌈-(χ + y i / ℓ)⌉ ⌊χ - y i / ℓ⌋ := by
      intro m hm
      rw [hTdef, Finset.mem_image] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      have hab := abs_le.mp (hcoord i n hn)
      rw [Finset.mem_Icc]
      constructor
      · rw [Int.ceil_le]; linarith [hab.1]
      · rw [Int.le_floor]; linarith [hab.2]
    have hcard : (T i).card ≤ (Finset.Icc ⌈-(χ + y i / ℓ)⌉ ⌊χ - y i / ℓ⌋).card :=
      Finset.card_le_card hTi
    have hIcc : ((Finset.Icc ⌈-(χ + y i / ℓ)⌉ ⌊χ - y i / ℓ⌋).card : ℝ) ≤ 2 * χ + 1 := by
      rw [Int.card_Icc]
      set z : ℤ := ⌊χ - y i / ℓ⌋ + 1 - ⌈-(χ + y i / ℓ)⌉ with hz
      by_cases hz0 : 0 ≤ z
      · have h1 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0]
        rw [h1]
        have hfl : (((⌊χ - y i / ℓ⌋ : ℤ)) : ℝ) ≤ χ - y i / ℓ := Int.floor_le _
        have hce : -(((⌈-(χ + y i / ℓ)⌉ : ℤ)) : ℝ) ≤ χ + y i / ℓ := by
          have h := Int.le_ceil (-(χ + y i / ℓ))
          linarith
        have hle : (z : ℝ) ≤ 2 * χ + 1 := by
          rw [hz]; push_cast; linarith
        exact hle
      · rw [Int.toNat_eq_zero.mpr (le_of_not_ge hz0)]
        push_cast
        linarith
    exact le_trans (by exact_mod_cast hcard) hIcc
  have hprod : (S.card : ℝ) ≤ ∏ _i : Fin 3, (2 * χ + 1) := by
    have hcard : S.card ≤ (Fintype.piFinset T).card := Finset.card_le_card hsub
    calc (S.card : ℝ) ≤ ((Fintype.piFinset T).card : ℝ) := by exact_mod_cast hcard
      _ = ∏ i : Fin 3, ((T i).card : ℝ) := by
            rw [Fintype.card_piFinset]
            exact Nat.cast_prod _ _
      _ ≤ ∏ _i : Fin 3, (2 * χ + 1) :=
            Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hTcard i)
  calc (S.card : ℝ) ≤ ∏ _i : Fin 3, (2 * χ + 1) := hprod
    _ = (2 * χ + 1) ^ 3 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## 3. The tiling identity for the lattice `ℓℤ³` -/

/-- Each point of `ℝ³` lies in exactly one translate `ℓn + cellI ℓ` of the half-open box. -/
lemma existsUnique_vadd_mem_cellI {ℓ : ℝ} (hℓ : 0 < ℓ) (x : EuclideanSpace ℝ (Fin 3)) :
    ∃! g : (latHom ℓ).range, g +ᵥ x ∈ cellI ℓ := by
  set n₀ : Fin 3 → ℤ := fun i => ⌈-(x i) / ℓ - 1 / 2⌉ with hn₀
  have hmem : ∀ i, (lat ℓ n₀ + x) i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2) := by
    intro i
    have hlo : -(x i) / ℓ - 1 / 2 ≤ ((n₀ i : ℤ) : ℝ) := by rw [hn₀]; exact Int.le_ceil _
    have hhi : ((n₀ i : ℤ) : ℝ) < -(x i) / ℓ - 1 / 2 + 1 := by
      rw [hn₀]; exact Int.ceil_lt_add_one _
    have h1 : -(ℓ / 2) ≤ ℓ * ((n₀ i : ℤ) : ℝ) + x i := by
      have h := mul_le_mul_of_nonneg_left hlo (le_of_lt hℓ)
      have he : ℓ * (-(x i) / ℓ - 1 / 2) = -x i - ℓ / 2 := by field_simp
      rw [he] at h; linarith
    have h2 : ℓ * ((n₀ i : ℤ) : ℝ) + x i < ℓ / 2 := by
      have h := mul_lt_mul_of_pos_left hhi hℓ
      have he : ℓ * (-(x i) / ℓ - 1 / 2 + 1) = -x i + ℓ / 2 := by field_simp; ring
      rw [he] at h; linarith
    rw [Set.mem_Ico]
    have hv : (lat ℓ n₀ + x) i = ℓ * ((n₀ i : ℤ) : ℝ) + x i := rfl
    rw [hv]
    exact ⟨h1, h2⟩
  refine ⟨⟨latHom ℓ n₀, AddMonoidHom.mem_range.mpr ⟨n₀, rfl⟩⟩, ?_, ?_⟩
  · intro i
    exact hmem i
  · intro g hg
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp g.2
    have hgi : (↑g : EuclideanSpace ℝ (Fin 3)) = lat ℓ m := by rw [← hm]; rfl
    have hcoord : ∀ i, ℓ * ((m i : ℤ) : ℝ) + x i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2) := by
      intro i
      have h : (g +ᵥ x) i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2) := hg i
      have hv : (g +ᵥ x) i = (↑g : EuclideanSpace ℝ (Fin 3)) i + x i := rfl
      have h2 : (↑g : EuclideanSpace ℝ (Fin 3)) i + x i = ℓ * ((m i : ℤ) : ℝ) + x i := by
        rw [hgi]; rfl
      rwa [hv, h2] at h
    have hm_i : ∀ i, m i = n₀ i := by
      intro i
      have h := hcoord i
      rw [Set.mem_Ico] at h
      have h1 : -(x i) / ℓ - 1 / 2 ≤ (m i : ℝ) := by
        have he : -(x i) / ℓ - 1 / 2 = (-ℓ / 2 - x i) / ℓ := by field_simp; ring
        rw [he, div_le_iff₀ hℓ]; linarith [h.1]
      have h2 : (m i : ℝ) < -(x i) / ℓ + 1 / 2 := by
        have he : -(x i) / ℓ + 1 / 2 = (ℓ / 2 - x i) / ℓ := by field_simp; ring
        rw [he, lt_div_iff₀ hℓ]; linarith [h.2]
      have ha : n₀ i ≤ m i := by rw [hn₀]; exact Int.ceil_le.mpr h1
      have hb : m i ≤ n₀ i := by
        rw [hn₀, Int.le_ceil_iff]
        push_cast
        linarith
      exact le_antisymm hb ha
    apply Subtype.ext
    rw [hgi, show m = n₀ from funext hm_i]
    rfl

/-- The half-open box is a fundamental domain of the lattice `ℓℤ³`. -/
theorem isAddFundamentalDomain_cellI {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.IsAddFundamentalDomain (latHom ℓ).range (cellI ℓ) MeasureTheory.volume :=
  MeasureTheory.IsAddFundamentalDomain.mk' (measurableSet_cellI ℓ).nullMeasurableSet
    (existsUnique_vadd_mem_cellI hℓ)

/-- **The tiling identity.**  Integrating over `ℝ³` is the same as summing the integrals of the
translates over one period cell. -/
theorem tiling_integral_cellI {ℓ : ℝ} (hℓ : 0 < ℓ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : EuclideanSpace ℝ (Fin 3) → E)
    (hf : MeasureTheory.Integrable f) :
    ∫ x, f x = ∑' n : Fin 3 → ℤ, ∫ x in cellI ℓ, f (x + lat ℓ n) := by
  haveI : Countable (latHom ℓ).range := countable_range_latHom (ne_of_gt hℓ)
  rw [(isAddFundamentalDomain_cellI hℓ).integral_eq_tsum'' f hf,
    ← (latEquiv (ne_of_gt hℓ)).tsum_eq (fun g : (latHom ℓ).range =>
      ∫ x in cellI ℓ, f (g +ᵥ x))]
  refine tsum_congr fun n => ?_
  congr 1 with x
  simp [latEquiv, add_comm]

/-- The tiling identity with the closed box. -/
theorem tiling_integral {ℓ : ℝ} (hℓ : 0 < ℓ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : EuclideanSpace ℝ (Fin 3) → E)
    (hf : MeasureTheory.Integrable f) :
    ∫ x, f x = ∑' n : Fin 3 → ℤ, ∫ x in cell ℓ, f (x + lat ℓ n) := by
  rw [tiling_integral_cellI hℓ f hf]
  exact tsum_congr fun n => setIntegral_cellI_eq_cell ℓ (fun x => f (x + lat ℓ n))

/-! ## 4. The Gram matrix of the box characters -/

/-- The box characters at the box-lattice momenta are orthogonal with weight `ℓ³`. -/
theorem gram_cell {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k k' : Work.BoseBoxFock.Lab N) :
    ∫ x, boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x
        * star (boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k') x)
      = if k = k' then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  have hpt : (fun x => boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x
        * star (boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k') x))
      = fun x => (cell ℓ).indicator (fun x => Complex.exp
          (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k
            - Work.BoseBoxFock.kmomLab ℓ N k') x : ℂ))) x :=
    funext fun x => boxChar_mul_star (cell ℓ) _ _ x
  rw [hpt, cell_eq_boxL, integral_indicator (measurableSet_boxL ℓ),
    kmomLab_sub ℓ N k k']
  rw [show (boxL ℓ) = {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ ℓ / 2} from rfl,
    box_exp_orthogonal hℓ (Work.BoseBoxFock.labVec N k - Work.BoseBoxFock.labVec N k')]
  rw [show ((ℓ : ℂ) ^ 3) = ((ℓ ^ 3 : ℝ) : ℂ) from (Complex.ofReal_pow ℓ 3).symm]
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [if_neg hkk, if_neg fun hm => hkk (labVec_injective N (sub_eq_zero.mp hm))]

/-! ## 5. Auxiliary computations for the Fourier coefficients -/

lemma star_boxChar_apply (B : Set (EuclideanSpace ℝ (Fin 3))) (q x : EuclideanSpace ℝ (Fin 3)) :
    star (boxChar B q x)
      = B.indicator (fun x => Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))) x := by
  by_cases hx : x ∈ B
  · rw [boxChar, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rw [show star (Complex.exp (Complex.I * (inner ℝ q x : ℂ)))
        = (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ q x : ℂ))) from rfl,
      ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · rw [boxChar, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, star_zero]

/-- The complex exponential of a real phase has modulus one. -/
lemma norm_exp_neg_I_mul_real (a : ℝ) : ‖Complex.exp (-(Complex.I * (a : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (a : ℂ)) = Complex.I * ((-a : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal]

lemma exp_phase_split (ℓ : ℝ) (q x : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ) :
    Complex.exp (-(Complex.I * (inner ℝ q (x + lat ℓ n) : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
        * Complex.exp (-(Complex.I * (inner ℝ q (lat ℓ n) : ℂ))) := by
  rw [inner_add_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## 6. The main theorem -/

theorem SamplingSqSumLeChiR0 {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ B : ℝ} (hℓ : 0 < ℓ)
    (hW : MeasureTheory.Integrable W) (hW2 : MeasureTheory.MemLp W 2)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hWnn : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ W x)
    (hWbd : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), W x ≤ B)
    (hB : 0 ≤ B) (N : ℕ) :
    ∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
      ≤ ℓ ^ 3 * (2 * Submission.BoseGases.chiR0 + 1) ^ 3 * B
          * ∫ x : EuclideanSpace ℝ (Fin 3), W x := by
  classical
  rcases le_or_gt R 0 with hR0 | hR0
  · -- `W` vanishes identically
    have hWz : ∀ x : EuclideanSpace ℝ (Fin 3), W x = 0 := by
      intro x
      by_contra hx
      have hmem : x ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hx)
      have hb := hsupp hmem
      rw [Metric.mem_ball, dist_zero_right] at hb
      linarith [norm_nonneg x]
    have hchat0 : ∀ q : EuclideanSpace ℝ (Fin 3), chat W q = 0 := by
      intro q
      have h0 : Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) q = 0 := by
        simp only [Submission.BoseGases.kinFT]
        rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
              Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * ((W y : ℝ) : ℂ)) = 0 from
            funext fun y => by rw [hWz y]; simp]
        simp
      rw [chat, h0, Complex.zero_re]
    have hInt0 : ∫ x : EuclideanSpace ℝ (Fin 3), W x = 0 := by
      rw [show W = 0 from funext hWz]; simp
    have hsum0 : ∑ k : Work.BoseBoxFock.Lab N,
        (chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hchat0]; ring
    rw [hsum0, hInt0]; simp
  · -- main case `0 < R`
    have hχpos : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
    have hχ : 0 ≤ Submission.BoseGases.chiR0 := le_of_lt hχpos
    set χ : ℝ := Submission.BoseGases.chiR0 with hχdef
    have hRℓ' : R ≤ ℓ * χ := hRℓ
    -- the periodisation
    set P : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun y => ∑ n ∈ latBox χ, W (y + lat ℓ n) with hPdef
    -- the a.e. bounds on `W` at the translates
    have htrans_le : ∀ c : EuclideanSpace ℝ (Fin 3), ∀ᵐ y ∂volume, W (y + c) ≤ B := by
      intro c
      have hmp : MeasureTheory.MeasurePreserving
          (fun y : EuclideanSpace ℝ (Fin 3) => y + c) volume volume :=
        ⟨measurable_id.add_const c, MeasureTheory.map_add_right_eq_self volume c⟩
      exact hmp.quasiMeasurePreserving.tendsto_ae.eventually hWbd
    have htrans_nn : ∀ c : EuclideanSpace ℝ (Fin 3), ∀ᵐ y ∂volume, 0 ≤ W (y + c) := by
      intro c
      have hmp : MeasureTheory.MeasurePreserving
          (fun y : EuclideanSpace ℝ (Fin 3) => y + c) volume volume :=
        ⟨measurable_id.add_const c, MeasureTheory.map_add_right_eq_self volume c⟩
      exact hmp.quasiMeasurePreserving.tendsto_ae.eventually hWnn
    have hble : ∀ᵐ y ∂volume, ∀ n ∈ latBox χ, W (y + lat ℓ n) ≤ B :=
      (eventually_all_finset _).mpr fun n _ => htrans_le (lat ℓ n)
    have hnn : ∀ᵐ y ∂volume, ∀ n ∈ latBox χ, 0 ≤ W (y + lat ℓ n) :=
      (eventually_all_finset _).mpr fun n _ => htrans_nn (lat ℓ n)
    -- pointwise bound on the periodisation
    have hPbound : ∀ᵐ y ∂volume, y ∈ cell ℓ → P y ≤ (2 * χ + 1) ^ 3 * B := by
      filter_upwards [hble] with y hb hy
      rw [hPdef]
      set S : Finset (Fin 3 → ℤ) :=
        (latBox χ).filter (fun n => y + lat ℓ n ∈ Metric.ball 0 R) with hSdef
      have hsub : S ⊆ latBox χ := Finset.filter_subset _ _
      have hzero : ∀ n ∈ latBox χ, n ∉ S → W (y + lat ℓ n) = 0 := by
        intro n hn hnS
        by_contra hne
        have : y + lat ℓ n ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R :=
          hsupp (subset_tsupport W (Function.mem_support.mpr hne))
        exact hnS (Finset.mem_filter.mpr ⟨hn, this⟩)
      have h1 : ∑ n ∈ latBox χ, W (y + lat ℓ n) = ∑ n ∈ S, W (y + lat ℓ n) :=
        (Finset.sum_subset hsub hzero).symm
      have h2 : ∑ n ∈ S, W (y + lat ℓ n) ≤ ∑ _n ∈ S, B :=
        Finset.sum_le_sum fun n hn => hb n (hsub hn)
      have hSp : ∀ n ∈ S, ‖y + lat ℓ n‖ ≤ R := by
        intro n hn
        have hlt : dist (y + lat ℓ n) (0 : EuclideanSpace ℝ (Fin 3)) < R :=
          (Finset.mem_filter.mp hn).2
        rw [dist_zero_right] at hlt
        exact le_of_lt hlt
      have h3 : (S.card : ℝ) ≤ (2 * χ + 1) ^ 3 :=
        card_le_of_norm_le hℓ hRℓ' hχ S hSp
      calc ∑ n ∈ latBox χ, W (y + lat ℓ n) = ∑ n ∈ S, W (y + lat ℓ n) := h1
        _ ≤ ∑ _n ∈ S, B := h2
        _ = (S.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * χ + 1) ^ 3 * B := mul_le_mul_of_nonneg_right h3 hB
    have hPnn : ∀ᵐ y ∂volume, 0 ≤ P y := by
      filter_upwards [hnn] with y hn
      rw [hPdef]
      exact Finset.sum_nonneg fun n hn' => hn n hn'
    have hPbound' : ∀ᵐ y ∂(volume.restrict (cell ℓ)), P y ≤ (2 * χ + 1) ^ 3 * B :=
      (MeasureTheory.ae_restrict_iff' (measurableSet_boxL ℓ)).mpr hPbound
    have hPnn' : ∀ᵐ y ∂(volume.restrict (cell ℓ)), 0 ≤ P y :=
      MeasureTheory.ae_mono Measure.restrict_le_self hPnn
    -- integrability and `L²` membership of the periodisation on the cell
    haveI : IsFiniteMeasure (volume.restrict (cell ℓ)) :=
      isFiniteMeasure_restrict.mpr (volume_boxL_ne_top ℓ)
    have hPmeas : AEStronglyMeasurable P (volume.restrict (cell ℓ)) := by
      have h : AEStronglyMeasurable (fun y => ∑ n ∈ latBox χ, W (y + lat ℓ n))
          (volume.restrict (cell ℓ)) := by
        rw [show (fun y => ∑ n ∈ latBox χ, W (y + lat ℓ n))
            = (∑ n ∈ latBox χ, fun y => W (y + lat ℓ n)) by
          funext y
          simp only [Finset.sum_apply]]
        exact Finset.aestronglyMeasurable_sum (latBox χ)
          (f := fun n y => W (y + lat ℓ n)) (μ := volume.restrict (cell ℓ))
          (fun n _ => ((hW.comp_add_right (lat ℓ n)).aestronglyMeasurable).mono_measure
            Measure.restrict_le_self)
      rw [hPdef]
      exact h
    have hPmemp : MeasureTheory.MemLp P 2 (volume.restrict (cell ℓ)) := by
      refine MeasureTheory.MemLp.of_bound hPmeas ((2 * χ + 1) ^ 3 * B) ?_
      filter_upwards [hPbound', hPnn'] with y hb hn
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact hb
    have hPint : IntegrableOn P (cell ℓ) volume :=
      hPmemp.integrable (by norm_num)
    -- `∫_{cell} P = ∫ W`
    have hIntP : ∫ y in cell ℓ, P y = ∫ x : EuclideanSpace ℝ (Fin 3), W x := by
      have ht : ∑' n : Fin 3 → ℤ, ∫ x in cell ℓ, W (x + lat ℓ n)
          = ∫ x : EuclideanSpace ℝ (Fin 3), W x := (tiling_integral hℓ W hW).symm
      have h1 : ∑' n : Fin 3 → ℤ, ∫ x in cell ℓ, W (x + lat ℓ n)
          = ∑ n ∈ latBox χ, ∫ x in cell ℓ, W (x + lat ℓ n) := by
        refine tsum_eq_sum fun n hn => ?_
        have : ∫ x in cell ℓ, W (x + lat ℓ n) = ∫ x in cell ℓ, (0 : ℝ) :=
          MeasureTheory.setIntegral_congr_fun (measurableSet_boxL ℓ)
            (fun x hx => eq_zero_of_notMem_latBox hℓ hRℓ' hsupp hn hx)
        rw [this, integral_zero]
      have h2 : ∑ n ∈ latBox χ, ∫ x in cell ℓ, W (x + lat ℓ n) = ∫ y in cell ℓ, P y := by
        rw [hPdef]
        rw [← MeasureTheory.integral_finsetSum (μ := volume.restrict (cell ℓ)) (latBox χ)
          (fun n _ => (hW.comp_add_right (lat ℓ n)).integrableOn)]
      exact h2.symm.trans (h1.symm.trans ht)
    -- the `L²` bound for `P` on the cell
    have hsq : ∫ y in cell ℓ, (P y) ^ 2 ≤ (2 * χ + 1) ^ 3 * B * ∫ y in cell ℓ, P y := by
      have hpoint : ∀ᵐ y ∂(volume.restrict (cell ℓ)), (P y) ^ 2
          ≤ (2 * χ + 1) ^ 3 * B * P y := by
        filter_upwards [hPbound', hPnn'] with y hb hn
        rw [sq]
        exact mul_le_mul_of_nonneg_right hb hn
      have hleft : Integrable (fun y => (P y) ^ 2) (volume.restrict (cell ℓ)) :=
        hPmemp.integrable_sq
      calc ∫ y in cell ℓ, (P y) ^ 2
          ≤ ∫ y in cell ℓ, (2 * χ + 1) ^ 3 * B * P y :=
            MeasureTheory.integral_mono_ae hleft
              (hPint.const_mul ((2 * χ + 1) ^ 3 * B)) hpoint
        _ = (2 * χ + 1) ^ 3 * B * ∫ y in cell ℓ, P y := by
            rw [MeasureTheory.integral_const_mul]
    -- the Fourier coefficients of the periodisation
    have hcoeff : ∀ k : Work.BoseBoxFock.Lab N,
        ∫ x, (((cell ℓ).indicator P x : ℝ) : ℂ)
            * star (boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x)
          = Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomLab ℓ N k) := by
      intro k
      set q : EuclideanSpace ℝ (Fin 3) := Work.BoseBoxFock.kmomLab ℓ N k with hq
      set g : EuclideanSpace ℝ (Fin 3) → ℂ := fun z =>
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) * ((W z : ℝ) : ℂ) with hgdef
      have hg_int : MeasureTheory.Integrable g := by
        rw [hgdef]
        exact MeasureTheory.Integrable.bdd_mul hW.ofReal
          (by fun_prop : AEStronglyMeasurable
            (fun z : EuclideanSpace ℝ (Fin 3) =>
              Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) volume)
          (Eventually.of_forall fun z => by rw [norm_exp_neg_I_mul_real])
      -- step 1: the star of a box character
      have h1 : (fun x => ((((cell ℓ).indicator P) x : ℝ) : ℂ)
            * star (boxChar (cell ℓ) q x))
          = fun x => (cell ℓ).indicator (fun x => ((P x : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))) x := by
        funext x
        by_cases hx : x ∈ cell ℓ
        · simp only [Set.indicator_of_mem hx, star_boxChar_apply]
        · simp only [Set.indicator_of_notMem hx, star_boxChar_apply, Complex.ofReal_zero,
            zero_mul]
      rw [h1]
      have key : ∫ x in cell ℓ, (fun x => ((P x : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))) x
          = ∫ x, (cell ℓ).indicator (fun x => ((P x : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))) x :=
        (MeasureTheory.integral_indicator (measurableSet_boxL ℓ)).symm
      rw [← key]
      -- step 2: expand the finite sum defining `P`
      have h2 : ∫ x in cell ℓ, ((P x : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
          = ∑ n ∈ latBox χ, ∫ x in cell ℓ, ((W (x + lat ℓ n) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) := by
        have hfun : ∀ x, ((P x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
            = ∑ n ∈ latBox χ, ((W (x + lat ℓ n) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) := by
          intro x
          rw [hPdef, show (fun y => ∑ n ∈ latBox χ, W (y + lat ℓ n)) x
              = ∑ n ∈ latBox χ, W (x + lat ℓ n) from rfl,
            Complex.ofReal_sum, Finset.sum_mul]
        have hint : ∀ n ∈ latBox χ, MeasureTheory.Integrable
            (fun x : EuclideanSpace ℝ (Fin 3) => ((W (x + lat ℓ n) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))
            (volume.restrict (boxL ℓ)) := by
          intro n _
          have hfun2 : (fun x : EuclideanSpace ℝ (Fin 3) => ((W (x + lat ℓ n) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))
              = fun x => Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
                * ((W (x + lat ℓ n) : ℝ) : ℂ) := by
            funext x; exact mul_comm _ _
          rw [hfun2]
          exact MeasureTheory.Integrable.bdd_mul
            ((hW.comp_add_right (lat ℓ n)).integrableOn.ofReal)
            (by fun_prop : AEStronglyMeasurable
              (fun x : EuclideanSpace ℝ (Fin 3) =>
                Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))
              (volume.restrict (boxL ℓ)))
            (Eventually.of_forall fun x => by rw [norm_exp_neg_I_mul_real])
        rw [show (cell ℓ : Set (EuclideanSpace ℝ (Fin 3))) = boxL ℓ from cell_eq_boxL ℓ,
          MeasureTheory.setIntegral_congr_fun (measurableSet_boxL ℓ) (fun x _ => hfun x),
          MeasureTheory.integral_finsetSum (latBox χ) hint]
      -- step 3: put each term in the form `g (x + ℓn)`
      have h3 : ∑ n ∈ latBox χ, ∫ x in cell ℓ, ((W (x + lat ℓ n) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
          = ∑ n ∈ latBox χ, ∫ x in cell ℓ, g (x + lat ℓ n) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        refine MeasureTheory.setIntegral_congr_fun (measurableSet_boxL ℓ) fun x _ => ?_
        have hphase : Complex.exp (-(Complex.I * (inner ℝ q (lat ℓ n) : ℂ))) = 1 := by
          rw [hq]
          exact exp_inner_kmomLab_lat (ne_of_gt hℓ) N k n
        simp only [hgdef]
        rw [exp_phase_split ℓ q x n, hphase, mul_one]
        exact mul_comm _ _
      -- step 4: sum over the lattice, then use the tiling identity
      have h4 : ∑ n ∈ latBox χ, ∫ x in cell ℓ, g (x + lat ℓ n) = ∫ z, g z := by
        have hz : ∀ n ∉ latBox χ, ∫ x in cell ℓ, g (x + lat ℓ n) = 0 := by
          intro n hn
          have hz0 : ∫ x in cell ℓ, g (x + lat ℓ n) = ∫ x in cell ℓ, (0 : ℂ) :=
            MeasureTheory.setIntegral_congr_fun (measurableSet_boxL ℓ) fun x hx => by
              simp only [hgdef]
              rw [eq_zero_of_notMem_latBox hℓ hRℓ' hsupp hn hx]
              simp
          rw [hz0, integral_zero]
        have htsum : ∑' n : Fin 3 → ℤ, ∫ x in cell ℓ, g (x + lat ℓ n) = ∫ z, g z :=
          (tiling_integral hℓ g hg_int).symm
        have hsum : ∑' n : Fin 3 → ℤ, ∫ x in cell ℓ, g (x + lat ℓ n)
            = ∑ n ∈ latBox χ, ∫ x in cell ℓ, g (x + lat ℓ n) := tsum_eq_sum hz
        exact hsum.symm.trans htsum
      have h5 : ∫ z, g z = Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) q := by
        simp only [hgdef, hq]
        rfl
      rw [h2, h3, h4, h5, hq]
    -- Bessel
    have hbessel := bessel_sum_integral
      (fun k : Work.BoseBoxFock.Lab N =>
        boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k))
      ((cell ℓ).indicator P) (L := ℓ ^ 3) (by positivity)
      (fun k => memLp_boxChar ℓ (Work.BoseBoxFock.kmomLab ℓ N k))
      (fun k k' => gram_cell hℓ N k k')
      ((MeasureTheory.integrable_indicator_iff (measurableSet_boxL ℓ)).mpr hPint)
      ((MeasureTheory.memLp_indicator_iff_restrict (measurableSet_boxL ℓ)).mpr hPmemp)
    -- final assembly
    calc ∑ k : Work.BoseBoxFock.Lab N,
          (chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
        ≤ ∑ k : Work.BoseBoxFock.Lab N,
            ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2 :=
          Finset.sum_le_sum fun k _ => re_sq_le_normSq _
      _ = ∑ k : Work.BoseBoxFock.Lab N,
            ‖∫ x, (((cell ℓ).indicator P x : ℝ) : ℂ)
              * star (boxChar (cell ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x)‖ ^ 2 :=
          Finset.sum_congr rfl fun k _ => by rw [hcoeff k]
      _ ≤ ℓ ^ 3 * ∫ x, ((cell ℓ).indicator P x) ^ 2 := hbessel
      _ = ℓ ^ 3 * ∫ y in cell ℓ, (P y) ^ 2 := by
          congr 1
          have key : ∫ y in cell ℓ, (P y) ^ 2
              = ∫ x, (cell ℓ).indicator (fun y => (P y) ^ 2) x :=
            (MeasureTheory.integral_indicator (measurableSet_boxL ℓ)).symm
          rw [key]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          by_cases hx : x ∈ cell ℓ
          · simp only [Set.indicator_of_mem hx]
          · simp only [Set.indicator_of_notMem hx]
            simp
      _ ≤ ℓ ^ 3 * ((2 * χ + 1) ^ 3 * B * ∫ y in cell ℓ, P y) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ℓ ^ 3 * (2 * χ + 1) ^ 3 * B * ∫ x : EuclideanSpace ℝ (Fin 3), W x := by
          rw [hIntP]; ring
      _ = ℓ ^ 3 * (2 * Submission.BoseGases.chiR0 + 1) ^ 3 * B
            * ∫ x : EuclideanSpace ℝ (Fin 3), W x := by rw [hχdef]

end Work.BoseFixR
