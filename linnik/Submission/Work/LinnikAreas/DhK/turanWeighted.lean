import Mathlib
import Submission.Work.LinnikAreas.DhK.TuranDefs
import Submission.Work.LinnikAreas.DhK.fejerCircleNonneg
import Submission.Work.LinnikAreas.DhK.fejerLowerCircleNonneg
import Submission.Work.LinnikAreas.DhK.fejerPointwise

/-!
# Turán's power-sum method, weighted form

We prove `Work.LinnikAreas.DhK.turanWeighted`, the weighted version of Turán's power-sum method
(Kadiri–Ng–Wong, arXiv:1902.08640, Theorem 2.2), used by the Deuring–Heilbronn repulsion argument.

The mathematical content is KNW §2:
* the Fejér-kernel identity `Σ_{j≤J}(1-j/(J+1))(1+cos jθ₀) Re s_j = Σ_i w_i (Q z_i + Q(z_i u)/2 +
  Q(z_i ū)/2)` for `u = z_{i₀}/‖z_{i₀}‖` (here `Q z = Σ_j (1-j/(J+1)) Re(z^j)`);
* the upper bound `≤ J · max_{j≤J} Re s_j`;
* the lower bound `≥ (J+1)/4 - 2M`, from the sharp Fejér bound `Q ζ ≥ -‖ζ‖/(1+‖ζ‖)` for `‖ζ‖ ≤ 1`
  (Mathlib's Poisson integral formula + the lower bound for the Herglotz–Riesz kernel), and
* `J = ⌊(8+ε)M⌋` with `M = Σ_i w_i ‖z_i‖/(‖z_{i₀}‖+‖z_i‖)`.
-/

namespace Work.LinnikAreas.DhK

open scoped BigOperators

/-! ### Arithmetic with the Fejér weights -/

lemma sum_Icc_one_cast_id (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (j : ℝ) = (J : ℝ) * ((J : ℝ) + 1) / 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1), ih]
      push_cast
      ring

lemma fejerW_eq (J j : ℕ) : fejerW J j = 1 - (j : ℝ) / ((J : ℝ) + 1) := by
  simp [fejerW]

lemma sum_fejerW (J : ℕ) : ∑ j ∈ Finset.Icc 1 J, fejerW J j = (J : ℝ) / 2 := by
  have hJ1 : ((J : ℝ) + 1) ≠ 0 := by positivity
  have hcard : (Finset.Icc 1 J).card = J := by rw [Nat.card_Icc]; omega
  have hsplit : ∑ j ∈ Finset.Icc 1 J, fejerW J j
      = (∑ j ∈ Finset.Icc 1 J, (1 : ℝ))
          - ∑ j ∈ Finset.Icc 1 J, (j : ℝ) / ((J : ℝ) + 1) := by
    simp only [fejerW_eq]
    rw [Finset.sum_sub_distrib]
  rw [hsplit, ← Finset.sum_div, Finset.sum_const, hcard, nsmul_eq_mul, sum_Icc_one_cast_id]
  field_simp
  ring

lemma fejerW_nonneg (J : ℕ) {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) : 0 ≤ fejerW J j := by
  have hJ : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  have h2 : (j : ℝ) / ((J : ℝ) + 1) ≤ 1 := (div_le_one hJ).mpr (by
    have : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
    linarith only [this])
  rw [fejerW_eq]
  linarith only [h2]

lemma fejerQ_at_one (J : ℕ) : fejerQ J 1 = (J : ℝ) / 2 := by
  rw [fejerQ]
  simp only [one_pow, Complex.one_re, mul_one]
  exact sum_fejerW J

/-! ### Summability of the power sums -/

lemma summable_pow_of_weyl {ι : Type*} (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hmax : ∀ i, ‖z i‖ ≤ 1)
    (hsum : Summable fun i => w i * (‖z i‖ / (1 + ‖z i‖))) (j : ℕ) (hj : 1 ≤ j) :
    Summable fun i => w i * (z i) ^ j := by
  apply Summable.of_norm_bounded (g := fun i => 2 * (w i * (‖z i‖ / (1 + ‖z i‖))))
  · exact hsum.mul_left 2
  · intro i
    have hr0 : 0 ≤ ‖z i‖ := norm_nonneg _
    have hpow : ‖z i‖ ^ j ≤ ‖z i‖ := by
      simpa using pow_le_pow_of_le_one hr0 (hmax i) hj
    have h1 : ‖z i‖ ≤ 2 * (‖z i‖ / (1 + ‖z i‖)) := by
      rw [show (2 : ℝ) * (‖z i‖ / (1 + ‖z i‖)) = 2 * ‖z i‖ / (1 + ‖z i‖) by ring,
        le_div_iff₀ (by linarith only [hr0] : (0 : ℝ) < 1 + ‖z i‖)]
      linarith only [mul_nonneg hr0 (sub_nonneg.mpr (hmax i)), hr0, hmax]
    have hnorm : ‖w i * (z i) ^ j‖ = w i * ‖z i‖ ^ j := by
      simp [abs_of_nonneg (hw i)]
    rw [hnorm]
    nlinarith only [hw i, h1, hpow, hw]

/-! ### Fejér estimates

The two analytic inputs, proved in the companion files of this directory, are
`Work.LinnikAreas.DhK.fejerCircleNonneg` (Fejér's inequality on the unit circle) and
`Work.LinnikAreas.DhK.fejerLowerCircleNonneg` (the Harnack/Poisson lower bound it implies),
together with the algebraic expansion `Work.LinnikAreas.DhK.fejerPointwise`. -/

/-- Sharp lower bound for the Fejér polynomial on the closed unit disc, from the classical
Harnack/Poisson bound (`Work.LinnikAreas.DhK.fejerLowerCircleNonneg`) applied to the Fejér
non-negativity on the unit circle (`Work.LinnikAreas.DhK.fejerCircleNonneg`). -/
lemma fejerQ_lower (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    -(‖z‖ / (1 + ‖z‖)) ≤ fejerQ J z :=
  fejerLowerCircleNonneg J (fun ζ hζ => fejerCircleNonneg J ζ hζ) z hz

/-- Expansion of `fejerK` as a weighted cosine sum. -/
lemma fejerK_expand (J : ℕ) (z u : ℂ) :
    fejerK J z u
      = ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) * (z ^ j).re :=
  (fejerPointwise J z u).symm

/-! ### Summability of the weighted Fejér kernels -/

lemma Summable.finset_sum' {ι : Type*} {β : Type*} {f : β → ι → ℝ} {s : Finset β}
    (h : ∀ j ∈ s, Summable (f j)) : Summable fun i => ∑ j ∈ s, f j i := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (summable_zero : Summable fun _ : ι => (0 : ℝ))
  | insert a s ha ih =>
      have hfun : (fun i => ∑ j ∈ insert a s, f j i)
          = fun i => f a i + ∑ j ∈ s, f j i := by
        funext i
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma summable_mul_fejerQ {ι : Type*} (J : ℕ) (w : ι → ℝ) (ζ : ι → ℂ)
    (hsp : ∀ j, 1 ≤ j → Summable fun i => w i * (ζ i) ^ j) :
    Summable fun i => w i * fejerQ J (ζ i) := by
  have hpt : ∀ i, w i * fejerQ J (ζ i)
      = ∑ j ∈ Finset.Icc 1 J, fejerW J j * (w i * ((ζ i) ^ j).re) := by
    intro i
    rw [fejerQ, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [funext hpt]
  apply Summable.finset_sum'
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hre : Summable fun i => (w i * (ζ i) ^ j).re :=
    (hsp j hj1).map Complex.reCLM (by continuity)
  have hre' : Summable fun i => w i * ((ζ i) ^ j).re :=
    hre.congr (fun i => by simp [Complex.mul_re])
  exact hre'.mul_left (fejerW J j)

lemma summable_mul_fejerK {ι : Type*} (J : ℕ) (w : ι → ℝ) (z : ι → ℂ) (u : ℂ)
    (hz : ∀ j, 1 ≤ j → Summable fun i => w i * (z i) ^ j)
    (hzu : ∀ j, 1 ≤ j → Summable fun i => w i * (z i * u) ^ j)
    (hzv : ∀ j, 1 ≤ j → Summable fun i => w i * (z i * star u) ^ j) :
    Summable fun i => w i * fejerK J (z i) u := by
  have h1 := summable_mul_fejerQ J w z hz
  have h2 := summable_mul_fejerQ J w (fun i => z i * u) hzu
  have h3 := summable_mul_fejerQ J w (fun i => z i * star u) hzv
  refine ((h1.add (h2.mul_left (1/2))).add (h3.mul_left (1/2))).congr (fun i => ?_)
  simp only [fejerK]
  ring

/-! ### The Turán identity -/

lemma fejer_tsum_identity {ι : Type*} (J : ℕ) (w : ι → ℝ) (z : ι → ℂ) (u : ℂ)
    (hsp : ∀ j, 1 ≤ j → Summable fun i => w i * (z i) ^ j) :
    ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) * (∑' i, w i * (z i) ^ j).re
      = ∑' i, w i * fejerK J (z i) u := by
  have hstep : ∀ j ∈ Finset.Icc 1 J,
      (∑' i, w i * (z i) ^ j).re = ∑' i, w i * ((z i) ^ j).re := by
    intro j hj
    have hsj := hsp j (Finset.mem_Icc.mp hj).1
    have h1 : (∑' i, w i * (z i) ^ j).re = ∑' i, (w i * (z i) ^ j).re := by
      have := hsj.map_tsum Complex.reCLM (by continuity)
      simpa using this
    rw [h1]
    exact tsum_congr (fun i => by simp [Complex.mul_re])
  rw [Finset.sum_congr rfl (fun j hj => by rw [hstep j hj])]
  have hs : ∀ j ∈ Finset.Icc 1 J,
      Summable fun i => (fejerW J j * (1 + (u ^ j).re)) * (w i * ((z i) ^ j).re) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hre : Summable fun i => (w i * (z i) ^ j).re :=
      (hsp j hj1).map Complex.reCLM (by continuity)
    have hre' : Summable fun i => w i * ((z i) ^ j).re :=
      hre.congr (fun i => by simp [Complex.mul_re])
    exact hre'.mul_left _
  have hswap :
      ∑ j ∈ Finset.Icc 1 J, (fejerW J j * (1 + (u ^ j).re)) * (∑' i, w i * ((z i) ^ j).re)
        = ∑' i, ∑ j ∈ Finset.Icc 1 J,
            (fejerW J j * (1 + (u ^ j).re)) * (w i * ((z i) ^ j).re) := by
    rw [Finset.sum_congr rfl (fun j _ =>
      (tsum_mul_left (f := fun i => w i * ((z i) ^ j).re)).symm)]
    exact (Summable.tsum_finsetSum
      (f := fun j i => (fejerW J j * (1 + (u ^ j).re)) * (w i * ((z i) ^ j).re)) hs).symm
  rw [hswap]
  apply tsum_congr
  intro i
  rw [fejerK_expand J (z i) u, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma fejerQ_lower_unit (J : ℕ) (u : ℂ) (hu : ‖u‖ = 1) : -(1/2 : ℝ) ≤ fejerQ J u := by
  have h := fejerQ_lower J u hu.le
  rw [hu] at h
  norm_num at h
  linarith only [h]

/-! ### The upper and lower bounds -/

lemma fejer_sum_le (J : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (S : ℕ → ℂ) (j₀ : ℕ)
    (hj₀ : j₀ ∈ Finset.Icc 1 J)
    (hmaxj : ∀ j ∈ Finset.Icc 1 J, (S j).re ≤ (S j₀).re) :
    ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) * (S j).re
      ≤ (∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re)) * (S j₀).re := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjmem := Finset.mem_Icc.mp hj
  have hw : 0 ≤ fejerW J j * (1 + (u ^ j).re) := by
    refine mul_nonneg (fejerW_nonneg J hjmem.1 hjmem.2) ?_
    have h1 : -1 ≤ (u ^ j).re := by
      have h := (abs_le.mp (Complex.abs_re_le_norm (u ^ j))).1
      rw [norm_pow, hu, one_pow] at h
      linarith only [h]
    linarith only [h1]
  exact mul_le_mul_of_nonneg_left (hmaxj j hj) hw

lemma fejer_weight_sum_le (J : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) ≤ J := by
  have h2 : ∀ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) ≤ fejerW J j * 2 := by
    intro j hj
    have hjmem := Finset.mem_Icc.mp hj
    have h1 : (u ^ j).re ≤ 1 := by
      have h := Complex.re_le_norm (u ^ j)
      rw [norm_pow, hu, one_pow] at h
      linarith only [h]
    nlinarith only [fejerW_nonneg J hjmem.1 hjmem.2, h1, hjmem]
  calc ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re)
      ≤ ∑ j ∈ Finset.Icc 1 J, fejerW J j * 2 := Finset.sum_le_sum h2
    _ = (∑ j ∈ Finset.Icc 1 J, fejerW J j) * 2 := by rw [Finset.sum_mul]
    _ = J := by rw [sum_fejerW]; ring

lemma fejer_sum_lower {ι : Type*} (J : ℕ) (w : ι → ℝ) (z : ι → ℂ) (u : ℂ) (i₀ : ι)
    (hw : ∀ i, 0 ≤ w i) (hwi₀ : 1 ≤ w i₀) (hmax : ∀ i, ‖z i‖ ≤ 1)
    (hunit : ‖u‖ = 1) (hzi₀ : z i₀ = u)
    (hKsum : Summable fun i => w i * fejerK J (z i) u)
    (hWsum : Summable fun i => w i * (‖z i‖ / (1 + ‖z i‖))) :
    (J : ℝ) / 4 + 1 / 4 - 2 * (∑' i, w i * (‖z i‖ / (1 + ‖z i‖)))
      ≤ ∑' i, w i * fejerK J (z i) u := by
  have hglb : ∀ i, 0 ≤ w i * (fejerK J (z i) u + 2 * (‖z i‖ / (1 + ‖z i‖))) := by
    intro i
    have h1 : -(‖z i‖ / (1 + ‖z i‖)) ≤ fejerQ J (z i) := fejerQ_lower J (z i) (hmax i)
    have h2 : -(‖z i‖ / (1 + ‖z i‖)) ≤ fejerQ J (z i * u) := by
      have h := fejerQ_lower J (z i * u) (by rw [norm_mul, hunit, mul_one]; exact hmax i)
      rwa [norm_mul, hunit, mul_one] at h
    have h3 : -(‖z i‖ / (1 + ‖z i‖)) ≤ fejerQ J (z i * star u) := by
      have h := fejerQ_lower J (z i * star u)
        (by rw [norm_mul, norm_star, hunit, mul_one]; exact hmax i)
      rwa [norm_mul, norm_star, hunit, mul_one] at h
    have h4 : fejerK J (z i) u
        = fejerQ J (z i) + (1/2) * fejerQ J (z i * u)
          + (1/2) * fejerQ J (z i * star u) := rfl
    rw [h4]
    nlinarith only [hw i, h1, hw, h2, h3]
  have hKi0 : ((J : ℝ) - 3) / 4 ≤ fejerK J u u := by
    have h1 : -(1/2 : ℝ) ≤ fejerQ J u := fejerQ_lower_unit J u hunit
    have h2 : -(1/2 : ℝ) ≤ fejerQ J (u * u) :=
      fejerQ_lower_unit J (u * u) (by simp [norm_mul, hunit])
    have h3 : fejerQ J (u * star u) = (J : ℝ) / 2 := by
      have huu : u * star u = 1 := by
        have h1 : u * star u = (Complex.normSq u : ℂ) := Complex.mul_conj u
        rw [h1, Complex.normSq_eq_norm_sq, hunit]
        norm_num
      rw [huu, fejerQ_at_one]
    simp only [fejerK]
    rw [h3]
    linarith only [h1, h2]
  have hgi0 : ((J : ℝ) + 1) / 4
      ≤ w i₀ * (fejerK J (z i₀) u + 2 * (‖z i₀‖ / (1 + ‖z i₀‖))) := by
    rw [hzi₀, hunit]
    norm_num
    have hKpos : 0 < fejerK J u u + 1 := by
      have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      linarith
    have hmul : 1 * (fejerK J u u + 1) ≤ w i₀ * (fejerK J u u + 1) :=
      mul_le_mul_of_nonneg_right hwi₀ hKpos.le
    linarith only [hKi0, hmul]
  have hgsum : Summable fun i => w i * (fejerK J (z i) u + 2 * (‖z i‖ / (1 + ‖z i‖))) := by
    refine (hKsum.add (hWsum.mul_left 2)).congr (fun i => ?_)
    ring
  have hg_tsum : ∑' i, w i * (fejerK J (z i) u + 2 * (‖z i‖ / (1 + ‖z i‖)))
      = (∑' i, w i * fejerK J (z i) u)
        + 2 * (∑' i, w i * (‖z i‖ / (1 + ‖z i‖))) := by
    rw [← tsum_mul_left]
    rw [← Summable.tsum_add hKsum (hWsum.mul_left 2)]
    exact tsum_congr (fun i => by ring)
  have hle : w i₀ * (fejerK J (z i₀) u + 2 * (‖z i₀‖ / (1 + ‖z i₀‖)))
      ≤ ∑' i, w i * (fejerK J (z i) u + 2 * (‖z i‖ / (1 + ‖z i‖))) :=
    Summable.le_tsum hgsum i₀ (fun j _ => hglb j)
  linarith only [hgi0, hle, hg_tsum]

/-! ### The normalised Turán lemma -/

lemma turanWeighted_unit (ε : ℝ) (hε : 0 < ε) {ι : Type*}
    (w : ι → ℝ) (z : ι → ℂ) (i₀ : ι)
    (hwi₀ : 1 ≤ w i₀) (hw : ∀ i, 0 ≤ w i)
    (hunit : ‖z i₀‖ = 1) (hmax : ∀ i, ‖z i‖ ≤ 1)
    (hsum : Summable fun i => w i * (‖z i‖ / (1 + ‖z i‖))) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ (8 + ε) * (∑' i, w i * (‖z i‖ / (1 + ‖z i‖))) ∧
      (ε / (32 + 4 * ε)) ≤ (∑' i, w i * (z i) ^ j).re := by
  set M : ℝ := ∑' i, w i * (‖z i‖ / (1 + ‖z i‖)) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact tsum_nonneg (fun i => mul_nonneg (hw i) (by positivity))
  have hMge : w i₀ / 2 ≤ M := by
    rw [hM]
    have h := Summable.le_tsum hsum i₀ (fun j _ => mul_nonneg (hw j) (by positivity))
    have hterm : w i₀ * (‖z i₀‖ / (1 + ‖z i₀‖)) = w i₀ / 2 := by rw [hunit]; ring
    linarith only [hterm, h]
  have hMhalf : (1 : ℝ) / 2 ≤ M := by linarith only [hwi₀, hMge]
  set J : ℕ := Nat.floor ((8 + ε) * M) with hJ
  have hxle : ((1 : ℕ) : ℝ) ≤ (8 + ε) * M := by
    have : (1 : ℝ) ≤ (8 + ε) * M := by nlinarith only [hwi₀, hMge, hε, hMnn]
    simpa using this
  have hJle : (J : ℝ) ≤ (8 + ε) * M := by
    rw [hJ]; exact Nat.floor_le (by linarith only [hxle])
  have hJlt : (8 + ε) * M < (J : ℝ) + 1 := by
    rw [hJ]; exact Nat.lt_floor_add_one _
  have hJ1 : 1 ≤ J := Nat.le_floor hxle
  have hsp : ∀ j, 1 ≤ j → Summable fun i => w i * (z i) ^ j :=
    fun j hj => summable_pow_of_weyl w z hw hmax hsum j hj
  have hspu : ∀ j, 1 ≤ j → Summable fun i => w i * (z i * (z i₀)) ^ j := by
    intro j hj
    have hsum_u : Summable fun i => w i * (‖z i * (z i₀)‖ / (1 + ‖z i * (z i₀)‖)) := by
      refine hsum.congr (fun i => ?_)
      rw [norm_mul, hunit, mul_one]
    have hmaxu : ∀ i, ‖z i * (z i₀)‖ ≤ 1 := by
      intro i; rw [norm_mul, hunit, mul_one]; exact hmax i
    exact summable_pow_of_weyl w (fun i => z i * (z i₀)) hw hmaxu hsum_u j hj
  have hspv : ∀ j, 1 ≤ j → Summable fun i => w i * (z i * star (z i₀)) ^ j := by
    intro j hj
    have hsum_v : Summable fun i => w i * (‖z i * star (z i₀)‖ / (1 + ‖z i * star (z i₀)‖)) := by
      refine hsum.congr (fun i => ?_)
      rw [norm_mul, norm_star, hunit, mul_one]
    have hmaxv : ∀ i, ‖z i * star (z i₀)‖ ≤ 1 := by
      intro i; rw [norm_mul, norm_star, hunit, mul_one]; exact hmax i
    exact summable_pow_of_weyl w (fun i => z i * star (z i₀)) hw hmaxv hsum_v j hj
  have hKsum : Summable fun i => w i * fejerK J (z i) (z i₀) :=
    summable_mul_fejerK J w z (z i₀) hsp hspu hspv
  set S : ℕ → ℂ := fun j => ∑' i, w i * (z i) ^ j with hS
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.Icc 1 J) (fun j => (S j).re) (by
    rw [Finset.nonempty_Icc]; exact hJ1)
  have hId : ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re) * (S j).re
      = ∑' i, w i * fejerK J (z i) (z i₀) := by
    rw [hS]
    exact fejer_tsum_identity J w z (z i₀) hsp
  have hub : ∑' i, w i * fejerK J (z i) (z i₀)
      ≤ (∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re)) * (S j₀).re := by
    rw [← hId]
    exact fejer_sum_le J (z i₀) hunit S j₀ hj₀mem hj₀max
  have hWnn : 0 ≤ ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjmem := Finset.mem_Icc.mp hj
    refine mul_nonneg (fejerW_nonneg J hjmem.1 hjmem.2) ?_
    have h1 : -1 ≤ ((z i₀) ^ j).re := by
      have h := (abs_le.mp (Complex.abs_re_le_norm ((z i₀) ^ j))).1
      rw [norm_pow, hunit, one_pow] at h
      linarith only [h]
    linarith only [h1]
  have hWle : ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re) ≤ J :=
    fejer_weight_sum_le J (z i₀) hunit
  have hlb : (J : ℝ) / 4 + 1 / 4 - 2 * M ≤ ∑' i, w i * fejerK J (z i) (z i₀) := by
    rw [hM]
    exact fejer_sum_lower J w z (z i₀) i₀ hw hwi₀ hmax hunit rfl hKsum hsum
  have hMpos : 0 < M := by linarith only [hwi₀, hMge]
  have hTgt : ε * M / 4 < ∑' i, w i * fejerK J (z i) (z i₀) := by
    have h2 : ε * M / 4 = ((8 + ε) * M) / 4 - 2 * M := by ring
    rw [h2]
    have h3 : ((8 + ε) * M) / 4 - 2 * M < (J : ℝ) / 4 + 1 / 4 - 2 * M := by linarith only [hJlt]
    linarith only [hJlt, hlb]
  have hpos1 : 0 < ε * M / 4 := by positivity
  have hWpos : 0 < (∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re)) * (S j₀).re :=
    lt_of_lt_of_le (lt_trans hpos1 hTgt) hub
  have hReS : 0 < (S j₀).re := by
    rcases lt_trichotomy (∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re)) 0
      with h | h | h
    · linarith only [hWnn, h]
    · rw [h, zero_mul] at hWpos
      exact absurd hWpos (lt_irrefl 0)
    · exact pos_of_mul_pos_right hWpos h.le
  have hkey : ε * M / 4 < J * (S j₀).re := by
    calc ε * M / 4 < ∑' i, w i * fejerK J (z i) (z i₀) := hTgt
      _ ≤ (∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + ((z i₀) ^ j).re)) * (S j₀).re := hub
      _ ≤ J * (S j₀).re := by nlinarith only [hWle, hReS]
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ1
  have h3 : ε * M / (4 * J) < (S j₀).re := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * J)]
    linarith only [hkey]
  have h4 : ε / (32 + 4 * ε) ≤ ε * M / (4 * J) := by
    have hJM : 4 * J ≤ 4 * ((8 + ε) * M) := by linarith only [hJle]
    have h1 : 1 / (4 * ((8 + ε) * M)) ≤ 1 / (4 * J) :=
      one_div_le_one_div_of_le (by positivity) hJM
    have h2 : ε * M / (4 * ((8 + ε) * M)) ≤ ε * M / (4 * J) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      simp only [one_div] at h1
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : ε / (32 + 4 * ε) = ε * M / (4 * ((8 + ε) * M)) := by
      rw [div_eq_div_iff (by positivity : (32 + 4 * ε) ≠ 0)
        (by positivity : (4 * ((8 + ε) * M)) ≠ 0)]
      ring
    rw [h5]
    exact h2
  exact ⟨j₀, (Finset.mem_Icc.mp hj₀mem).1, by
      have : (j₀ : ℝ) ≤ (J : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj₀mem).2
      linarith only [hJle, this],
    le_of_lt (lt_of_le_of_lt h4 h3)⟩

/-! ### Main statement -/

/-- **Turán's power-sum method, weighted form** (Kadiri–Ng–Wong, arXiv:1902.08640, Theorem 2.2, generalised to a non-negative weight `w` on an arbitrary index type `ι`).

Let `w : ι → ℝ` be non-negative with `1 ≤ w i₀`, let `z : ι → ℂ` be nonzero at `i₀` with
`‖z i‖ ≤ ‖z i₀‖` for all `i`, and assume the weighted "Weyl sum"
`M = ∑' i, w i * (‖z i‖ / (‖z i₀‖ + ‖z i‖))` is finite. Then there is a power `1 ≤ j ≤ (8+ε)M` for
which the weighted power sum has real part at least `(ε/(32+4ε))‖z i₀‖^j`.

This is the ingredient used by the Deuring–Heilbronn repulsion argument of Kadiri–Ng–Wong (used
there with `b_n ≡ 1`); the weights here are zero multiplicities. In the source the Weyl sum appears
as `b_1^{-1}∑ b_n |z_n|/(|z_1|+|z_n|)` and the conclusion as `b_1 ε/(32+4ε)|z_1|^j`; we have
normalised `b_1 ≥ 1`, which gives the constant `ε/(32+4ε)` here.

Proof route (KNW §2, Theorem 2.2): normalise `‖z i₀‖ = 1` (the claim is invariant under scaling all
`z i` by a fixed positive constant). With the Fejér-kernel weights
`P(r,θ) = ∑_{j=1}^{J} (1 - j/(J+1)) r^j cos(jθ)` one has
`∑_{j=1}^{J}(1-j/(J+1)) (Re s_j)(1+cos(jθ i₀)) = ∑_i w i (P(r_i,θ_i) + P(r_i,θ_i-θ_i₀)/2 + P(r_i,θ_i+θ_i₀)/2)`
(where `z i = r_i e^{iθ_i}`), the left side is at most `J · max_{1≤j≤J} Re s_j`, the term `i = i₀` is
bounded below using `P(1,0) = J/2` together with the Fejér bound `P(r,θ) ≥ -(1/2)` respectively
`≥ -r/(1+r)`, and the remaining terms by `≥ -2∑_{i≠i₀} w i r_i/(1+r_i)`. Taking `J = ⌊(8+ε)M⌋`
(with `M` the Weyl sum) gives the conclusion; the sharp Fejér bound is
`Work.LinnikAreas.DhK.fejerQ_lower`, proved from Fejér's non-negativity of the kernel on the unit
circle (`Work.LinnikAreas.DhK.fejerCircleNonneg`) by the classical Harnack/Poisson bound for a
harmonic function of positive part (`Work.LinnikAreas.DhK.fejerLowerCircleNonneg`). -/
theorem turanWeighted (ε : ℝ) (hε : 0 < ε) {ι : Type*}
    (w : ι → ℝ) (z : ι → ℂ) (i₀ : ι)
    (hwi₀ : 1 ≤ w i₀) (hw : ∀ i, 0 ≤ w i) (hzi₀ : z i₀ ≠ 0)
    (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖)
    (hsum : Summable fun i => w i * (‖z i‖ / (‖z i₀‖ + ‖z i‖))) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ (8 + ε) * (∑' i, w i * (‖z i‖ / (‖z i₀‖ + ‖z i‖))) ∧
      (ε / (32 + 4 * ε)) * ‖z i₀‖ ^ j ≤ (∑' i, w i * (z i) ^ j).re := by
  have hRpos : 0 < ‖z i₀‖ := norm_pos_iff.mpr hzi₀
  have hnorm' : ∀ i, ‖z i / (‖z i₀‖ : ℂ)‖ = ‖z i‖ / ‖z i₀‖ := by
    intro i
    rw [norm_div]
    simp [abs_of_pos hRpos]
  have hunit' : ‖z i₀ / (‖z i₀‖ : ℂ)‖ = 1 := by
    rw [hnorm']
    exact div_self (ne_of_gt hRpos)
  have hmax' : ∀ i, ‖z i / (‖z i₀‖ : ℂ)‖ ≤ 1 := by
    intro i
    rw [hnorm', div_le_one hRpos]
    exact hmax i
  have hkey_eq : ∀ i, ‖z i / (‖z i₀‖ : ℂ)‖ / (1 + ‖z i / (‖z i₀‖ : ℂ)‖)
      = ‖z i‖ / (‖z i₀‖ + ‖z i‖) := by
    intro i
    rw [hnorm']
    field_simp
  have hsum' : Summable fun i =>
      w i * (‖z i / (‖z i₀‖ : ℂ)‖ / (1 + ‖z i / (‖z i₀‖ : ℂ)‖)) :=
    hsum.congr (fun i => by rw [hkey_eq i])
  obtain ⟨j, hj1, hjle, hjbound⟩ :=
    turanWeighted_unit ε hε w (fun i => z i / (‖z i₀‖ : ℂ)) i₀ hwi₀ hw hunit' hmax' hsum'
  refine ⟨j, hj1, ?_, ?_⟩
  · have hMeq : (∑' i, w i * (‖z i / (‖z i₀‖ : ℂ)‖ / (1 + ‖z i / (‖z i₀‖ : ℂ)‖)))
        = (∑' i, w i * (‖z i‖ / (‖z i₀‖ + ‖z i‖))) := by
      apply tsum_congr
      intro i
      rw [hkey_eq i]
    rw [hMeq] at hjle
    exact hjle
  · have hzpow : ∀ i, (z i / (‖z i₀‖ : ℂ)) ^ j
        = (((‖z i₀‖ ^ j)⁻¹ : ℝ) : ℂ) * (z i) ^ j := by
      intro i
      rw [div_eq_mul_inv, mul_pow, inv_pow, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
      ring
    have hsum_eq : ∑' i, w i * (z i / (‖z i₀‖ : ℂ)) ^ j
        = (((‖z i₀‖ ^ j)⁻¹ : ℝ) : ℂ) * (∑' i, w i * (z i) ^ j) := by
      have hpt : ∀ i, (w i : ℂ) * (z i / (‖z i₀‖ : ℂ)) ^ j
          = (((‖z i₀‖ ^ j)⁻¹ : ℝ) : ℂ) * ((w i : ℂ) * (z i) ^ j) := by
        intro i
        rw [hzpow i]
        ring
      rw [tsum_congr hpt, tsum_mul_left]
    have hRe : (∑' i, w i * (z i / (‖z i₀‖ : ℂ)) ^ j).re
        = (‖z i₀‖ ^ j)⁻¹ * (∑' i, w i * (z i) ^ j).re := by
      rw [hsum_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hRj : 0 < ‖z i₀‖ ^ j := pow_pos hRpos j
    have h5 : ε / (32 + 4 * ε) * ‖z i₀‖ ^ j ≤ (∑' i, w i * (z i) ^ j).re := by
      have h6 := hjbound
      rw [hRe] at h6
      have h7 : ‖z i₀‖ ^ j * (ε / (32 + 4 * ε))
          ≤ ‖z i₀‖ ^ j * ((‖z i₀‖ ^ j)⁻¹ * (∑' i, w i * (z i) ^ j).re) :=
        mul_le_mul_of_nonneg_left h6 hRj.le
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hRj), one_mul] at h7
      linarith only [h7]
    exact h5

end Work.LinnikAreas.DhK
