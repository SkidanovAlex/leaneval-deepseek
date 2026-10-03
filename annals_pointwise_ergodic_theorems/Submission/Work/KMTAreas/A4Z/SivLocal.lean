
/-
# siv-second from struct-iii-second: removing the support hypotheses

Krause--Mirek--Tao, 5.2.  Corollary siv-second -- the l2 bound for the minor-arc part of the
second dual function -- for arbitrary f in l2(Z) and bounded h, deduced from Corollary
struct-iii-second (the same bound for f, h supported in a window of length ~ N^d) using the
off-diagonal decay of the Ionescu--Wainger projections.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.kmtProj_comp_add
import Submission.Work.KMTAreas.A4Z.SivOff
import Submission.Work.KMTAreas.A4Z.memLp_ahalfTransposeTwo_of_bdd
import Submission.Work.KMTAreas.A4Z.schur_finite
import Submission.Work.KMTAreas.A4Z.kernel_sum_le
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A4.offYoung
import Submission.Work.KMTAreas.A4.memLp_two_count_summable_norm_sq
import Submission.Work.KMTAreas.A7.ProjBound
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTAreas.A5 (BoundedZ boundedZ_add)

namespace Work.KMTAreas.A4Z

theorem one_le_blockLen (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ blockLen P N := by
  rw [blockLen]
  have h1 : (1 : ℕ) ≤ N ^ P.natDegree :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega : N ≠ 0))
  exact_mod_cast h1

theorem N_le_blockLen (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℤ) ≤ blockLen P N := by
  rw [blockLen]
  have h1 : N ≤ N ^ P.natDegree := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN (by omega)
  exact_mod_cast h1

theorem eval_le_coeffSum {P : Polynomial ℤ} {N : ℕ} (hN : 1 ≤ N) {n : ℤ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ (N : ℤ)) : |P.eval n| ≤ coeffSum P * blockLen P N := by
  rw [Polynomial.eval_eq_sum]
  have hn0 : (0 : ℤ) ≤ n := le_trans (by norm_num) hn1
  calc |∑ j ∈ P.support, P.coeff j * n ^ j|
      ≤ ∑ j ∈ P.support, |P.coeff j * n ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ P.support, |P.coeff j| * n ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hn0 j)]
    _ ≤ ∑ j ∈ P.support, |P.coeff j| * blockLen P N := by
        refine Finset.sum_le_sum fun j hj => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hjle : j ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
        calc n ^ j ≤ (N : ℤ) ^ j := pow_le_pow_left₀ hn0 hn2 j
          _ ≤ (N : ℤ) ^ P.natDegree := by
              have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
              exact pow_le_pow_right₀ hN1 hjle
          _ = blockLen P N := by rw [blockLen]; exact (Nat.cast_pow N P.natDegree).symm
    _ = coeffSum P * blockLen P N := by rw [coeffSum, Finset.sum_mul]

theorem eval_sub_self_le {P : Polynomial ℤ} (hP : 2 ≤ P.natDegree) {N : ℕ} (hN : 1 ≤ N)
    {n : ℤ} (hn1 : (N : ℤ) / 2 < n) (hn2 : n ≤ (N : ℤ)) :
    |P.eval n - n| ≤ shiftBd P N := by
  have hn1' : 1 ≤ n := by
    have h0 : (0 : ℤ) ≤ (N : ℤ) / 2 := Int.ediv_nonneg (by positivity) (by norm_num)
    omega
  have hP1 : |P.eval n| ≤ coeffSum P * blockLen P N := eval_le_coeffSum hN hn1' hn2
  have hn_le : |n| ≤ blockLen P N := by
    rw [abs_of_nonneg (le_trans (by norm_num) hn1')]
    exact le_trans hn2 (N_le_blockLen P hP hN)
  rw [shiftBd]
  calc |P.eval n - n| ≤ |P.eval n| + |n| := abs_sub _ _
    _ ≤ coeffSum P * blockLen P N + blockLen P N := add_le_add hP1 hn_le
    _ = (coeffSum P + 1) * blockLen P N := by ring

theorem zPiece_dPiece_support (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {N : ℕ} (hN : 1 ≤ N)
    (f h : ℤ → ℂ) (i : ℤ) :
    ∀ x : ℤ, dPiece P N f h i x ≠ 0 → x ∈ suppWin P N i := by
  intro x hx
  rw [dPiece, AhalfTranspose₂] at hx
  have hLpos : 0 < blockLen P N := lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)
  obtain ⟨n, hn, hne⟩ : ∃ n ∈ Finset.Ioc (N / 2) N,
      zPiece (blockLen P N) f i (x + (n : ℤ) - P.eval (n : ℤ))
        * (hWin P N i).indicator h (x - P.eval (n : ℤ)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (by rw [Finset.sum_eq_zero hc, mul_zero])
  have hz : zPiece (blockLen P N) f i (x + (n : ℤ) - P.eval (n : ℤ)) ≠ 0 :=
    fun h0 => hne (by rw [h0, zero_mul])
  have hs := zPiece_support hLpos hz
  obtain ⟨hnlow, hnhigh⟩ := Finset.mem_Ioc.mp hn
  have hn1 : (N : ℤ) / 2 < (n : ℤ) := by
    have : ((N / 2 : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast hnlow
    rwa [Int.natCast_ediv] at this
  have hn2 : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hnhigh
  have hshift := eval_sub_self_le hP hN hn1 hn2
  rw [suppWin, Set.mem_Icc]
  obtain ⟨hbd1, hbd2⟩ := abs_le.mp hshift
  constructor <;> linarith [hs.1, hs.2, hbd1, hbd2]

theorem le_ediv_of_mul_le {L : ℤ} (hL : 0 < L) {k x : ℤ} (h : k * L ≤ x) : k ≤ x / L := by
  by_contra hc
  push_neg at hc
  have h4 : x / L + 1 ≤ k := Int.lt_iff_add_one_le.mp hc
  have h5 : (x / L + 1) * L ≤ k * L := Int.mul_le_mul_of_nonneg_right h4 hL.le
  have hx : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hem : x % L < L := Int.emod_lt_of_pos x hL
  have h6 : ((x / L) + 1) * L = L * (x / L) + L := by ring
  nlinarith [h, h5, hx, hem, h6]

theorem ediv_mem_suppWin {P : Polynomial ℤ} {N : ℕ} (hN : 1 ≤ N) {i x : ℤ}
    (hx : x ∈ suppWin P N i) : |x / blockLen P N - i| ≤ coeffSum P + 2 := by
  rw [suppWin, Set.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hLpos : 0 < blockLen P N := lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)
  have hshift : shiftBd P N = (coeffSum P + 1) * blockLen P N := rfl
  rw [hshift] at hx1
  have hle : i - (coeffSum P + 1) ≤ x / blockLen P N := by
    refine le_ediv_of_mul_le hLpos ?_
    have hkey : i * blockLen P N - (coeffSum P + 1) * blockLen P N
        = (i - (coeffSum P + 1)) * blockLen P N := by ring
    linarith [hx1, hkey]
  have hlt : x / blockLen P N < i + coeffSum P + 3 := by
    have h1 : (i + 1) * blockLen P N + (coeffSum P + 1) * blockLen P N
        = (i + coeffSum P + 2) * blockLen P N := by ring
    have h2 : (i + coeffSum P + 2) * blockLen P N
        < (i + coeffSum P + 3) * blockLen P N := by
      have h3 : (i + coeffSum P + 3) * blockLen P N
          = (i + coeffSum P + 2) * blockLen P N + blockLen P N := by ring
      rw [h3]; exact lt_add_of_pos_right _ hLpos
    exact Int.ediv_lt_of_lt_mul hLpos (by linarith [hx2, h1, h2])
  refine abs_le.mpr ⟨by linarith, by linarith⟩

theorem dPiece_eq (P : Polynomial ℤ) (N : ℕ) {f h : ℤ → ℂ} (hN : 1 ≤ N) (i : ℤ) :
    dPiece P N f h i = AhalfTranspose₂ N P (zPiece (blockLen P N) f i) h := by
  funext x
  simp only [dPiece, AhalfTranspose₂]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hnlow, hnhigh⟩ := Finset.mem_Ioc.mp hn
  have hnle : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hnhigh
  have hLpos : 0 < blockLen P N := lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)
  by_cases hz : zPiece (blockLen P N) f i (x + (n : ℤ) - P.eval (n : ℤ)) = 0
  · rw [hz, zero_mul, zero_mul]
  · have hs := zPiece_support hLpos hz
    have hmem : x - P.eval (n : ℤ) ∈ hWin P N i := by
      rw [hWin, Set.mem_Icc]
      constructor
      · linarith [hs.1, hnle]
      · have : (0 : ℤ) ≤ (n : ℤ) := by positivity
        linarith [hs.2, this]
    rw [Set.indicator_of_mem hmem]

theorem AhalfTranspose2_comp_add (N : ℕ) (P : Polynomial ℤ) (t : ℤ) (f h : ℤ → ℂ) :
    AhalfTranspose₂ N P (fun x : ℤ => f (x + t)) (fun x : ℤ => h (x + t))
      = fun x : ℤ => AhalfTranspose₂ N P f h (x + t) := by
  funext x
  have hterm : ∀ n ∈ Finset.Ioc (N / 2) N,
      f (x + (n : ℤ) - P.eval (n : ℤ) + t) * h (x - P.eval (n : ℤ) + t)
        = f ((x + t) + (n : ℤ) - P.eval (n : ℤ)) * h ((x + t) - P.eval (n : ℤ)) := by
    intro n _
    have h1 : x + (n : ℤ) - P.eval (n : ℤ) + t = (x + t) + (n : ℤ) - P.eval (n : ℤ) := by ring
    have h2 : x - P.eval (n : ℤ) + t = (x + t) - P.eval (n : ℤ) := by ring
    rw [h1, h2]
  simp only [AhalfTranspose₂]
  rw [Finset.sum_congr rfl hterm]

/-- **Translation invariance of the minor-arc part** (a `1 - Π` applied to `Ã_N^{**}`). -/
theorem minorPart_comp_add (N : ℕ) (P : Polynomial ℤ) (ρ : ℝ) (l : ℕ) (t : ℤ)
    (ψ χ : ℤ → ℂ) :
    (fun y : ℤ => AhalfTranspose₂ N P (fun z => ψ (z + t)) (fun z => χ (z + t)) y
        - projTwo P ρ N l (AhalfTranspose₂ N P (fun z => ψ (z + t))
            (fun z => χ (z + t))) y)
      = fun y : ℤ => (fun x : ℤ => AhalfTranspose₂ N P ψ χ x
          - projTwo P ρ N l (AhalfTranspose₂ N P ψ χ) x) (y + t) := by
  funext y
  simp only [projTwo_apply]
  rw [AhalfTranspose2_comp_add N P t ψ χ,
    kmtProj_comp_add ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) t (AhalfTranspose₂ N P ψ χ)]

/-- **`eLpNorm` form of the translation invariance of the minor-arc part.** -/
theorem eLpNorm_minorPart_comp_add (N : ℕ) (P : Polynomial ℤ) (ρ : ℝ) (l : ℕ) (t : ℤ)
    (ψ χ : ℤ → ℂ) :
    eLpNorm (fun y : ℤ => AhalfTranspose₂ N P (fun z => ψ (z + t)) (fun z => χ (z + t)) y
        - projTwo P ρ N l (AhalfTranspose₂ N P (fun z => ψ (z + t))
            (fun z => χ (z + t))) y) 2 Measure.count
      = eLpNorm (fun x : ℤ => AhalfTranspose₂ N P ψ χ x
          - projTwo P ρ N l (AhalfTranspose₂ N P ψ χ) x) 2 Measure.count := by
  rw [minorPart_comp_add N P ρ l t ψ χ]
  exact eLpNorm_comp_add_count (fun x : ℤ => AhalfTranspose₂ N P ψ χ x
    - projTwo P ρ N l (AhalfTranspose₂ N P ψ χ) x) 2 t

theorem local_bound (P : Polynomial ℤ) {c ρ Cρ : ℝ} {C : NNReal}
    (hS : StructIiiSecondHyp P c ρ Cρ C) {N l : ℕ} (hN : 1 ≤ N)
    (hgood : GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)))
    {a b : ℤ} {ψ χ : ℤ → ℂ}
    (hψ : MemLp ψ 2 Measure.count) (hχ : ∀ x : ℤ, ‖χ x‖ ≤ 1)
    (hψs : ∀ x : ℤ, x < a ∨ b < x → ψ x = 0) (hχs : ∀ x : ℤ, x < a ∨ b < x → χ x = 0)
    (hlen : b - a ≤ 2 * ((N : ℤ) ^ P.natDegree)) :
    eLpNorm (fun x : ℤ =>
        AhalfTranspose₂ N P ψ χ x - projTwo P ρ N l (AhalfTranspose₂ N P ψ χ) x) 2 Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm ψ 2 Measure.count := by
  set L : ℤ := (N : ℤ) ^ P.natDegree with hLdef
  set N₀ : ℕ := N ^ P.natDegree with hN₀def
  have hLI : L = (N₀ : ℤ) := by rw [hLdef, hN₀def]; push_cast; ring
  have hLpos : 0 < L := by rw [hLdef]; positivity
  set t : ℤ := b - L with ht
  have keyψ : ∀ y : ℤ, ψ (y + t) ≠ 0 → -L ≤ y ∧ y ≤ L := by
    intro y hne
    have h1 : ¬(y + t < a ∨ b < y + t) := fun hc => hne (hψs (y + t) hc)
    push_neg at h1
    rw [ht] at h1
    constructor <;> omega
  have keyχ : ∀ y : ℤ, χ (y + t) ≠ 0 → -L ≤ y ∧ y ≤ L := by
    intro y hne
    have h1 : ¬(y + t < a ∨ b < y + t) := fun hc => hne (hχs (y + t) hc)
    push_neg at h1
    rw [ht] at h1
    constructor <;> omega
  have hsuppψ : SupportIn (fun y : ℤ => ψ (y + t)) N₀ := by
    intro y hy
    by_contra hne
    obtain ⟨h2, h3⟩ := keyψ y hne
    have h4 : (y.natAbs : ℤ) ≤ L := by
      rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h2, h3⟩
    rw [hLI] at h4
    omega
  have hsuppχ : SupportIn (fun y : ℤ => χ (y + t)) N₀ := by
    intro y hy
    by_contra hne
    obtain ⟨h2, h3⟩ := keyχ y hne
    have h4 : (y.natAbs : ℤ) ≤ L := by
      rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h2, h3⟩
    rw [hLI] at h4
    omega
  have hmemψ : MemLp (fun y : ℤ => ψ (y + t)) 2 Measure.count := by
    refine MeasureTheory.memLp_iff.mpr ?_
    rw [lt_top_iff_ne_top, eLpNorm_comp_add_count ψ 2 t]
    exact hψ.eLpNorm_lt_top.ne
  have hbdχ : ∀ y : ℤ, ‖χ (y + t)‖ ≤ 1 := fun y => hχ (y + t)
  have hN₀cast : (N₀ : ℝ) = (N : ℝ) ^ P.natDegree := by
    rw [hN₀def]; push_cast; ring
  have hmain := hS N N₀ l (fun y : ℤ => ψ (y + t)) (fun y : ℤ => χ (y + t)) hN
    (by rw [hN₀cast]
        linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (N : ℝ) by positivity) (P.natDegree : ℝ)])
    (by rw [hN₀cast])
    hsuppψ hsuppχ hmemψ hbdχ hgood
  rw [eLpNorm_minorPart_comp_add N P ρ l t ψ χ, eLpNorm_comp_add_count ψ 2 t] at hmain
  exact hmain

theorem kmtProj_l2_bound (ρ : ℝ) (l : ℕ) (k : ℤ) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ u : ℤ → ℂ,
      eLpNorm (Work.KMTContract.kmtProj ρ l k u) 2 Measure.count
        ≤ C * eLpNorm u 2 Measure.count := by
  refine ⟨∑' t : ℤ, ENNReal.ofReal ‖Work.KMTAreas.A5.kmtKern ρ l k t‖, ?_, ?_⟩
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => norm_nonneg _)
      (Work.KMTAreas.A5.summable_kmtKern_norm ρ l k)]
    exact ENNReal.ofReal_ne_top
  · intro u
    have hconv : Work.KMTContract.kmtProj ρ l k u
        = fun n : ℤ => ∑' j : ℤ, Work.KMTAreas.A5.kmtKern ρ l k j * u (n - j) :=
      funext fun n => Work.KMTAreas.A5.kmtProj_eq_conv ρ l k u n
    rw [hconv]
    simpa using Work.KMTAreas.A4.offYoung_conv_count_le (p := 2) (by norm_num) _ _

theorem enorm_bilinPair_le_of_memLp {u v : ℤ → ℂ}
    (hu : MemLp u 2 Measure.count) (hv : MemLp v 2 Measure.count) :
    ‖bilinPair u v‖ₑ ≤ eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  have h1 : ‖bilinPair u v‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := by
    rw [bilinPair]
    exact enorm_tsum_le_tsum_enorm
  have h2 : (∑' x : ℤ, ‖u x * v x‖ₑ) = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := by
    simp only [eLpNorm_one_eq_lintegral_enorm MeasureTheory.AEStronglyMeasurable.of_discrete, lintegral_count, enorm_mul]
  have h3 : eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count
      ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) (measurable_of_countable u).aestronglyMeasurable (measurable_of_countable v).aestronglyMeasurable (by filter_upwards with x; simp) (p := 2) (q := 2) (r := 1)
  calc ‖bilinPair u v‖ₑ ≤ ∑' x : ℤ, ‖u x * v x‖ₑ := h1
    _ = eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count := h2
    _ ≤ 1 * eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := h3
    _ = eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by ring

theorem enorm_pairing_le_mul {u v : ℤ → ℂ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hu : eLpNorm u 2 Measure.count ≤ ENNReal.ofReal A)
    (hv : eLpNorm v 2 Measure.count ≤ ENNReal.ofReal A') :
    ‖∑' x : ℤ, u x * star (v x)‖ ≤ A * A' := by
  have hstar : eLpNorm (fun x : ℤ => star (v x)) 2 Measure.count = eLpNorm v 2 Measure.count :=
    eLpNorm_star
  have h1 : ‖∑' x : ℤ, u x * star (v x)‖ₑ ≤ ENNReal.ofReal (A * A') := by
    have hum : MemLp u 2 Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hu ENNReal.ofReal_lt_top)
    have hvm : MemLp (fun x : ℤ => star (v x)) 2 Measure.count := by
      refine MeasureTheory.memLp_iff.mpr ?_
      rw [lt_top_iff_ne_top,
        show eLpNorm (fun x : ℤ => star (v x)) 2 Measure.count = eLpNorm v 2 Measure.count
          from eLpNorm_star]
      exact (lt_of_le_of_lt hv ENNReal.ofReal_lt_top).ne
    have := enorm_bilinPair_le_of_memLp hum hvm
    rw [bilinPair] at this
    refine this.trans ?_
    rw [hstar]
    calc eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count
        ≤ ENNReal.ofReal A * ENNReal.ofReal A' := mul_le_mul' hu hv
      _ = ENNReal.ofReal (A * A') := (ENNReal.ofReal_mul hA).symm
  have h2 : ENNReal.ofReal ‖∑' x : ℤ, u x * star (v x)‖ ≤ ENNReal.ofReal (A * A') := by
    rw [← show ‖∑' x : ℤ, u x * star (v x)‖ₑ
        = ENNReal.ofReal ‖∑' x : ℤ, u x * star (v x)‖ from by simp [enorm_eq_nnnorm]]
    exact h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hA')).mp h2

theorem coeffSum_nonneg (P : Polynomial ℤ) : 0 ≤ coeffSum P :=
  Finset.sum_nonneg fun j _ => abs_nonneg _


theorem GoodMajorArcs.mono {ρ Cρ Cρ' : ℝ} {l : ℕ} {k : ℤ}
    (h : GoodMajorArcs ρ Cρ l k) (hle : Cρ' ≤ Cρ) : GoodMajorArcs ρ Cρ' l k := by
  rw [GoodMajorArcs] at h ⊢
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
  linarith [h, mul_le_mul_of_nonneg_right hle h2]

theorem enorm_block_le {L : ℤ} {m : ℤ} {g : ℤ → ℂ} :
    eLpNorm (fun x : ℤ => if x ∈ Finset.Ico (m * L) ((m + 1) * L) then g x else 0)
        2 Measure.count ≤ eLpNorm g 2 Measure.count := by
  refine eLpNorm_mono (hf := by pw_aesm) fun x => ?_
  split_ifs with hx
  · exact le_rfl
  · simp

theorem zPiece_memLp {L : ℤ} {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (i : ℤ) :
    MemLp (zPiece L f i) 2 Measure.count := by
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [lt_top_iff_ne_top]
  exact (lt_of_le_of_lt (eLpNorm_mono (hf := by pw_aesm) (f := zPiece L f i) (g := f) fun x => by
    rw [zPiece_apply]
    split_ifs with h
    · exact le_rfl
    · simp) hf.eLpNorm_lt_top).ne

/-- Bookkeeping identity: `ofReal (C * x * y)` is the product of the `ENNReal`s. -/
theorem ofReal_coe_mul_mul {C : ℝ≥0} {x y : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal ((C : ℝ) * x * y)
      = (C : ENNReal) * ENNReal.ofReal x * ENNReal.ofReal y := by
  rw [ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg C) hx)]
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  rw [show ((C : ENNReal)) = ENNReal.ofReal ((C : ℝ)) from (ENNReal.ofReal_coe_nnreal).symm]

theorem pairing_boundA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {c ρ Cρ : ℝ} {C : NNReal}
    (hS : StructIiiSecondHyp P c ρ Cρ C) {N l : ℕ} (hN : 1 ≤ N)
    (hgood : GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)))
    {f h : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (i j : ℤ) :
    ‖∑' x : ℤ, (dPiece P N f h i x - projTwo P ρ N l (dPiece P N f h i) x)
        * star (dPiece P N f h j x - projTwo P ρ N l (dPiece P N f h j) x)‖
      ≤ ((C : ℝ) * (2 : ℝ) ^ (-(c * (l : ℝ)))) ^ 2
          * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) := by
  set A : ℝ := (C : ℝ) * (2 : ℝ) ^ (-(c * (l : ℝ))) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hLpos : 0 < blockLen P N := lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)
  have hloc : ∀ i : ℤ,
      eLpNorm (fun x : ℤ => dPiece P N f h i x - projTwo P ρ N l (dPiece P N f h i) x)
          2 Measure.count
        ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f i)) := by
    intro i
    have hmem : MemLp (zPiece (blockLen P N) f i) 2 Measure.count := zPiece_memLp hf i
    have hχ : ∀ x : ℤ, ‖(hWin P N i).indicator h x‖ ≤ 1 := by
      intro x
      by_cases hx : x ∈ hWin P N i
      · rw [Set.indicator_of_mem hx]; exact hh x
      · rw [Set.indicator_of_notMem hx]; simp
    have hψs : ∀ x : ℤ, x < i * blockLen P N - (N : ℤ) ∨ (i + 1) * blockLen P N < x →
        zPiece (blockLen P N) f i x = 0 := by
      intro x hx
      by_contra hne
      have hs := zPiece_support hLpos hne
      rcases hx with hx | hx <;> omega
    have hχs : ∀ x : ℤ, x < i * blockLen P N - (N : ℤ) ∨ (i + 1) * blockLen P N < x →
        (hWin P N i).indicator h x = 0 := by
      intro x hx
      rw [Set.indicator_of_notMem]
      rw [hWin, Set.mem_Icc]
      rintro ⟨h1, h2⟩
      rcases hx with hx | hx <;> omega
    have hlen : (i + 1) * blockLen P N - (i * blockLen P N - (N : ℤ))
        ≤ 2 * ((N : ℤ) ^ P.natDegree) := by
      have hNL : (N : ℤ) ≤ blockLen P N := N_le_blockLen P hP hN
      have hcast : (N : ℤ) ^ P.natDegree = blockLen P N :=
        (Nat.cast_pow N P.natDegree).symm
      rw [hcast]
      linarith
    have hmain := local_bound P hS hN hgood hmem hχ hψs hχs hlen
    have hd : dPiece P N f h i
        = AhalfTranspose₂ N P (zPiece (blockLen P N) f i) ((hWin P N i).indicator h) := rfl
    rw [eLpNorm_two_eq_ofReal_l2norm (summable_norm_sq_zPiece hLpos f i)] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [← ofReal_coe_mul_mul (C := C) (x := (2 : ℝ) ^ (-(c * (l : ℝ))))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  have h1 := enorm_pairing_le_mul (A := A * l2norm (zPiece (blockLen P N) f i))
    (A' := A * l2norm (zPiece (blockLen P N) f j))
    (mul_nonneg hA0 (l2norm_nonneg _)) (mul_nonneg hA0 (l2norm_nonneg _))
    (hloc i) (hloc j)
  calc ‖∑' x : ℤ, (dPiece P N f h i x - projTwo P ρ N l (dPiece P N f h i) x)
        * star (dPiece P N f h j x - projTwo P ρ N l (dPiece P N f h j) x)‖
      ≤ (A * l2norm (zPiece (blockLen P N) f i)) * (A * l2norm (zPiece (blockLen P N) f j)) := h1
    _ = A ^ 2 * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) := by ring
    _ = ((C : ℝ) * (2 : ℝ) ^ (-(c * (l : ℝ)))) ^ 2
          * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) := by rw [hA]


/-- The remainder of `f` after removing the block pieces indexed by `S`. -/
def blockRemainder (L : ℤ) (f : ℤ → ℂ) (S : Finset ℤ) : ℤ → ℂ :=
  fun x => f x - ∑ i ∈ S, zPiece L f i x

/-! ## The pieces lie in `ℓ²`, and the operator `T` is `ℓ²`-bounded -/

/-- Additivity of the second dual function in its first argument. -/
theorem ahalfTransposeTwo_add (N : ℕ) (P : Polynomial ℤ) (f g h : ℤ → ℂ) :
    AhalfTranspose₂ N P (f + g) h = AhalfTranspose₂ N P f h + AhalfTranspose₂ N P g h := by
  funext x
  simp only [AhalfTranspose₂, Pi.add_apply, add_mul, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]

/-- The `i`-th local dual function is in `ℓ²`. -/
theorem memLp_dPiece (P : Polynomial ℤ) (N : ℕ) {f h : ℤ → ℂ} (hN : 1 ≤ N)
    (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (i : ℤ) :
    MemLp (dPiece P N f h i) 2 Measure.count := by
  have hχ : ∀ x : ℤ, ‖(hWin P N i).indicator h x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ hWin P N i
    · rw [Set.indicator_of_mem hx]; exact hh x
    · rw [Set.indicator_of_notMem hx]; simp
  exact (memLp_ahalfTransposeTwo_of_bdd N P hN (zPiece_memLp hf i) hχ).1

/-- The minor-arc part of the `i`-th block piece is in `ℓ²`. -/
theorem memLp_minorPart (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ} (hN : 1 ≤ N)
    (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (i : ℤ) :
    MemLp (minorPart P ρ N l f h i) 2 Measure.count := by
  have h1 : MemLp (dPiece P N f h i) 2 Measure.count := memLp_dPiece P N hN hf hh i
  have h2 : MemLp (projTwo P ρ N l (dPiece P N f h i)) 2 Measure.count := by
    obtain ⟨M, hM, hMbd⟩ := kmtProj_l2_bound ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
    refine MeasureTheory.memLp_iff.mpr ?_
    rw [lt_top_iff_ne_top, projTwo_apply]
    have hle := hMbd (dPiece P N f h i)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hM h1.eLpNorm_lt_top.ne) hle
  exact h1.sub h2

/-- The squared moduli of the minor-arc part of a block piece are summable. -/
theorem summable_norm_sq_minorPart (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ}
    (hN : 1 ≤ N) (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (i : ℤ) :
    Summable (fun x : ℤ => ‖minorPart P ρ N l f h i x‖ ^ 2) :=
  Work.KMTAreas.A4.memLp_two_count_summable_norm_sq (memLp_minorPart P ρ N l hN hf hh i)

/-- The total mass `∑_m (1+|m|)^{-8}` of the power-decay kernel of the Schur estimate. -/
noncomputable def kern8Mass : ℝ := ∑' m : ℤ, (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))

/-- **The power-decay kernel `(1+|m|)^{-8}` is summable on `ℤ`.** -/
theorem summable_pow8 :
    Summable (fun m : ℤ => (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
  have hg : Summable (fun n : ℤ => (1 : ℝ) / |(((n : ℤ) : ℝ))| ^ (8 : ℝ)) := by
    simpa using (Real.summable_one_div_int_add_rpow 0 8).mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
  have h1 : (1 : ℝ) ≤ |(((m : ℤ) : ℝ))| := by
    have h := Int.one_le_abs hm
    have hcast : ((|m| : ℤ) : ℝ) = |(((m : ℤ) : ℝ))| := Int.cast_abs
    rw [← hcast]
    exact_mod_cast h
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))
      ≤ |(((m : ℤ) : ℝ))| ^ (-(8 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one h1) (by linarith) (by norm_num)
    _ = 1 / |(((m : ℤ) : ℝ))| ^ (8 : ℝ) := by
        rw [Real.rpow_neg (abs_nonneg _), one_div]


/-- **The local `ℓ²` bound for the minor-arc part of a block piece** (from
`struct-iii-second`, applied after translating the support window into `[-N^d,N^d]`). -/
theorem localBoundAll (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {c ρ Cρ : ℝ} {C : NNReal}
    (hS : StructIiiSecondHyp P c ρ Cρ C) {N l : ℕ} (hN : 1 ≤ N)
    (hgood : GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)))
    {f h : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (i : ℤ) :
    eLpNorm (minorPart P ρ N l f h i) 2 Measure.count
      ≤ ENNReal.ofReal (((C : ℝ) * (2 : ℝ) ^ (-(c * (l : ℝ))))
          * l2norm (zPiece (blockLen P N) f i)) := by
  have hLpos : 0 < blockLen P N := lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)
  have hmem : MemLp (zPiece (blockLen P N) f i) 2 Measure.count := zPiece_memLp hf i
  have hχ : ∀ x : ℤ, ‖(hWin P N i).indicator h x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ hWin P N i
    · rw [Set.indicator_of_mem hx]; exact hh x
    · rw [Set.indicator_of_notMem hx]; simp
  have hψs : ∀ x : ℤ, x < i * blockLen P N - (N : ℤ) ∨ (i + 1) * blockLen P N < x →
      zPiece (blockLen P N) f i x = 0 := by
    intro x hx
    by_contra hne
    have hs := zPiece_support hLpos hne
    rcases hx with hx | hx <;> omega
  have hχs : ∀ x : ℤ, x < i * blockLen P N - (N : ℤ) ∨ (i + 1) * blockLen P N < x →
      (hWin P N i).indicator h x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem]
    rw [hWin, Set.mem_Icc]
    rintro ⟨h1, h2⟩
    rcases hx with hx | hx <;> omega
  have hlen : (i + 1) * blockLen P N - (i * blockLen P N - (N : ℤ))
      ≤ 2 * ((N : ℤ) ^ P.natDegree) := by
    have hNL : (N : ℤ) ≤ blockLen P N := N_le_blockLen P hP hN
    have hcast : (N : ℤ) ^ P.natDegree = blockLen P N :=
      (Nat.cast_pow N P.natDegree).symm
    rw [hcast]
    linarith
  have hmain := local_bound P hS hN hgood hmem hχ hψs hχs hlen
  rw [eLpNorm_two_eq_ofReal_l2norm (summable_norm_sq_zPiece hLpos f i)] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [← ofReal_coe_mul_mul (C := C) (x := (2 : ℝ) ^ (-(c * (l : ℝ))))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

/-- **Additivity of `T = (1-Π)Ã_N^{**}(·,h)`** on functions whose dual functions are bounded. -/
theorem transOp_add_of_bdd (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {f g h : ℤ → ℂ}
    (hf : BoundedZ (AhalfTranspose₂ N P f h)) (hg : BoundedZ (AhalfTranspose₂ N P g h)) :
    transOp P ρ N l (f + g) h = transOp P ρ N l f h + transOp P ρ N l g h := by
  have hfg : BoundedZ (AhalfTranspose₂ N P (f + g) h) := by
    rw [ahalfTransposeTwo_add N P f g h]; exact boundedZ_add hf hg
  have hkey : Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
        (AhalfTranspose₂ N P (f + g) h)
      = Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
          (AhalfTranspose₂ N P f h)
        + Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
          (AhalfTranspose₂ N P g h) := by
    rw [ahalfTransposeTwo_add N P f g h]
    exact Work.KMTAreas.A5.kmtProj_add_bounded ρ l _ hf hg
  funext x
  simp only [transOp_apply, projTwo_apply, Pi.add_apply]
  rw [hkey]
  simp only [Pi.add_apply]
  rw [ahalfTransposeTwo_add N P f g h]
  simp only [Pi.add_apply]
  ring

/-- Triangle inequality for a difference of sequences. -/
theorem eLpNorm_sub_le' {A B : ℤ → ℂ} :
    eLpNorm (fun x : ℤ => A x - B x) 2 Measure.count
      ≤ eLpNorm (fun x : ℤ => A x) 2 Measure.count
        + eLpNorm (fun x : ℤ => B x) 2 Measure.count := by
  have h2 : (fun x : ℤ => (- B) x) = -(fun x : ℤ => B x) := rfl
  have h3 : (fun x : ℤ => A x - B x) = (fun x : ℤ => A x + (- B) x) := rfl
  calc eLpNorm (fun x : ℤ => A x - B x) 2 Measure.count
      = eLpNorm (fun x : ℤ => A x + (- B) x) 2 Measure.count := by rw [h3]
    _ ≤ eLpNorm (fun x : ℤ => A x) 2 Measure.count
        + eLpNorm (fun x : ℤ => (- B) x) 2 Measure.count :=
        MeasureTheory.eLpNorm_add_le (μ := Measure.count) (p := 2) (by norm_num)
    _ = eLpNorm (fun x : ℤ => A x) 2 Measure.count
        + eLpNorm (fun x : ℤ => B x) 2 Measure.count := by
        rw [h2, MeasureTheory.eLpNorm_neg]

/-- **`T = (1-Π)Ã_N^{**}(·,h)` is bounded on `ℓ²`.** -/
theorem eLpNorm_transOp_le (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {h : ℤ → ℂ}
    (hN : 1 ≤ N) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ g : ℤ → ℂ,
      eLpNorm (transOp P ρ N l g h) 2 Measure.count ≤ M * eLpNorm g 2 Measure.count := by
  obtain ⟨Md, hMd, hPid⟩ := kmtProj_l2_bound ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))
  refine ⟨1 + Md, ?_, fun g => ?_⟩
  · rw [ENNReal.add_ne_top]; exact ⟨ENNReal.one_ne_top, hMd⟩
  · have h1 : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h x) 2 Measure.count
        ≤ eLpNorm g 2 Measure.count := eLpNorm_ahalfTransposeTwo_le N P hN hh
    have h2 : eLpNorm (fun x : ℤ => projTwo P ρ N l (AhalfTranspose₂ N P g h) x) 2 Measure.count
        ≤ Md * eLpNorm g 2 Measure.count := by
      have hle := hPid (AhalfTranspose₂ N P g h)
      rw [projTwo_apply]
      exact hle.trans (mul_le_mul' le_rfl h1)
    have hsub : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h x
          - projTwo P ρ N l (AhalfTranspose₂ N P g h) x) 2 Measure.count
        ≤ eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h x) 2 Measure.count
          + eLpNorm (fun x : ℤ => projTwo P ρ N l (AhalfTranspose₂ N P g h) x)
              2 Measure.count :=
      eLpNorm_sub_le' (A := fun x : ℤ => AhalfTranspose₂ N P g h x)
        (B := fun x : ℤ => projTwo P ρ N l (AhalfTranspose₂ N P g h) x)
    calc eLpNorm (transOp P ρ N l g h) 2 Measure.count
        = eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h x
            - projTwo P ρ N l (AhalfTranspose₂ N P g h) x) 2 Measure.count := rfl
      _ ≤ eLpNorm (fun x : ℤ => AhalfTranspose₂ N P g h x) 2 Measure.count
            + eLpNorm (fun x : ℤ => projTwo P ρ N l (AhalfTranspose₂ N P g h) x)
                2 Measure.count := hsub
      _ ≤ eLpNorm g 2 Measure.count + Md * eLpNorm g 2 Measure.count := add_le_add h1 h2
      _ = (1 + Md) * eLpNorm g 2 Measure.count := by ring

end Work.KMTAreas.A4Z

