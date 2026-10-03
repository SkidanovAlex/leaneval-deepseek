/-
# Area A4Z: the arc projection of §5.2 with both spatial tail clauses

`Work.KMTAreas.A4Z.projectionSelf` is the projection step of Proposition `lip-2` (§5.2) in its
free-window form *with the two spatial tail clauses*: the explicit windowed projection
`G = star (win M s * g)` has `ℤ`-Fourier support in the arc of radius `1/M` around `-s`, pairs
with `g` by at least the windowed `L²`-mass `B`, has `ℓ¹`-mass `≤ C ∑‖g‖`, has `ℓ¹`-mass at most
`C M` outside the window `[-A N^d, A N^d]` in which `g` lives, and has `ℓ²`-mass at most
`C² R⁻¹ N^d` outside `[-R N^d, R N^d]` for every `R ≥ 1`.

The proof is the construction of `Work.KMTAreas.A4Z.projectionTail` (the pairing clause is the
Parseval identity `⟨g, star (win M s * g)⟩ = ∫₀¹ ‖kmtFhat g‖² winFT M s`), together with
* `Work.KMTAreas.A4Z.lip2FringeWin` for the `ℓ¹`-fringe, and
* `Work.KMTAreas.A4Z.projectionL2Decay` for the `ℓ²`-decay.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Projection
import Submission.Work.KMTAreas.A4Z.lip2FringeWin
import Submission.Work.KMTAreas.A4Z.projectionL2Decay

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.KMTAreas.A4Z

open Work.Analysis.InverseTheory

theorem projectionSelf (P : Polynomial ℤ) :
    ∀ (A : ℝ), 1 ≤ A → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (N₀ : ℕ), (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      ∀ (g : ℤ → ℂ), Summable (fun x : ℤ => ‖g x‖) → (∀ x : ℤ, ‖g x‖ ≤ 1) →
        Work.Analysis.InverseTheory.SupportIn g N₀ →
      ∀ (M s B : ℝ), 2 ≤ M →
        B ≤ ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re →
        ∃ G : ℤ → ℂ,
          (∀ x : ℤ, ‖G x‖ ≤ C) ∧ Summable (fun x : ℤ => ‖G x‖) ∧
          (∑' x : ℤ, ‖G x‖) ≤ C * ∑' x : ℤ, ‖g x‖ ∧
          Work.Analysis.InverseTheory.FourierSupportIn G
            (Work.KMTAreas.A4.arcSet (-(((s : ℝ)) : Work.Analysis.InverseTheory.FreqCircle))
              (1 / M)) ∧
          B ≤ ‖Work.Analysis.InverseTheory.bilinPair g G‖ ∧
          (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0))
            ≤ C * M ∧
          (∀ R : ℝ, 1 ≤ R →
            (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0))
              ≤ C ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree) := by
  intro A hA
  obtain ⟨C₀, hC₀pos, hC₀le⟩ := Work.KMTAreas.A4.win_tsum_le
  obtain ⟨Cf, hCfpos, hFri⟩ := lip2FringeWin P
  obtain ⟨Cd, hCdpos, hDec⟩ := projectionL2Decay P A hA
  set C : ℝ := max (max C₀ 1) (max Cf Cd) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le (lt_of_lt_of_le hC₀pos (le_max_left C₀ 1)) (le_max_left _ _)
  have hC₀C : C₀ ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left C₀ 1) (le_max_left _ _)
  have hCfC : Cf ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left Cf Cd) (le_max_right (max C₀ 1) _)
  have hCdC : Cd ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right Cf Cd) (le_max_right (max C₀ 1) _)
  have h1C : (1 : ℝ) ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right C₀ 1) (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro N hN N₀ hN₀le g hgsum hgbd hsupp M s B hM hB
  have hMpos : (0 : ℝ) < M := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  set w : ℤ → ℂ := Work.KMTAreas.A4.win M ((s : ℝ) : FreqCircle) with hwdef
  have hwsum : Summable fun m : ℤ => ‖w m‖ := by
    rw [hwdef]; exact Work.KMTAreas.A4.win_summable M hM1 _
  have hwC : (∑' m : ℤ, ‖w m‖) ≤ C₀ := by
    rw [hwdef]; exact hC₀le M _ hM1
  have hz := Work.KMTAreas.A4.zConvL1 w g hwsum hgsum hgbd
  have hwin : FourierSupportIn w (Work.KMTAreas.A4.arcSet ((s : ℝ) : FreqCircle) (1 / M)) ∧
      (∀ t : ℝ, Work.KMTAreas.A4.winFT M s t = ((Work.KMTAreas.A4.winFT M s t).re : ℂ)) := by
    rw [hwdef]
    exact Work.KMTAreas.A4.winPackage M s hM
  set F : ℤ → ℂ := fun x => ∑' m : ℤ, w m * g (x - m) with hFdef
  have hFsum : Summable fun x : ℤ => ‖F x‖ := hz.1
  have hF1 : (∑' x : ℤ, ‖F x‖) ≤ (∑' m : ℤ, ‖w m‖) * ∑' m : ℤ, ‖g m‖ := hz.2.1
  have hFsup : ∀ x : ℤ, ‖F x‖ ≤ ∑' m : ℤ, ‖w m‖ := hz.2.2.1
  have hFZ : ∀ ξ : FreqCircle, ZFourier F ξ = ZFourier w ξ * ZFourier g ξ := hz.2.2.2
  -- the pairing, by Parseval
  have hwinreal : ∀ t : ℝ, star (Work.KMTAreas.A4.winFT M s t) = Work.KMTAreas.A4.winFT M s t := by
    intro t; rw [hwin.2 t]; exact Complex.conj_ofReal _
  have hwZF : ∀ t : ℝ, ZFourier w ((t : ℝ) : FreqCircle) = Work.KMTAreas.A4.winFT M s t := by
    intro t
    rw [hwdef]
    exact Work.KMTAreas.A4.winZFourier M s t hMpos
  have hhatF : ∀ t : ℝ, Work.A3.kmtFhat F t
      = Work.KMTAreas.A4.winFT M s t * Work.A3.kmtFhat g t := by
    intro t
    rw [Work.KMTAreas.A4.kmtFhat_eq_ZFourier F t, hFZ, hwZF t,
      ← Work.KMTAreas.A4.kmtFhat_eq_ZFourier g t]
  have hkey : ∀ t : ℝ, Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t)
      = (((‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ)) : ℂ) := by
    intro t
    have hst : star (Work.KMTAreas.A4.winFT M s t) = Work.KMTAreas.A4.winFT M s t := hwinreal t
    have hconj : Work.A3.kmtFhat g t * star (Work.A3.kmtFhat g t)
        = (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hstarF : star (Work.A3.kmtFhat F t)
        = Work.KMTAreas.A4.winFT M s t * star (Work.A3.kmtFhat g t) := by
      rw [hhatF t, star_mul, hst]
      ring
    calc Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t)
        = Work.A3.kmtFhat g t * (Work.KMTAreas.A4.winFT M s t
            * star (Work.A3.kmtFhat g t)) := by rw [hstarF]
      _ = Work.KMTAreas.A4.winFT M s t
            * (Work.A3.kmtFhat g t * star (Work.A3.kmtFhat g t)) := by ring
      _ = Work.KMTAreas.A4.winFT M s t * (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by
            rw [hconj]
      _ = (((Work.KMTAreas.A4.winFT M s t).re : ℝ) : ℂ)
            * (((‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ)) : ℂ) := by
            rw [hwin.2 t, Complex.ofReal_re]
      _ = (((Work.KMTAreas.A4.winFT M s t).re * ‖Work.A3.kmtFhat g t‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.ofReal_mul]
      _ = (((‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ)) : ℂ) := by
            rw [mul_comm]
  have hInt : (∫ t in (0 : ℝ)..1, Work.A3.kmtFhat g t * star (Work.A3.kmtFhat F t))
      = (((∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun t _ => hkey t
  have hpair : B ≤ ‖Work.Analysis.InverseTheory.bilinPair g (fun x => star (F x))‖ := by
    show B ≤ ‖(∑' x : ℤ, g x * star (F x))‖
    rw [Work.KMTAreas.A4.kmtFhatParseval g F hgsum hFsum, hInt]
    calc B ≤ (∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ) := hB
      _ = ((( ∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ)) : ℂ).re :=
          (Complex.ofReal_re _).symm
      _ ≤ ‖((( ∫ t in (0 : ℝ)..1,
          ‖Work.A3.kmtFhat g t‖ ^ 2 * (Work.KMTAreas.A4.winFT M s t).re : ℝ)) : ℂ)‖ :=
          Complex.re_le_norm _
  -- identify `star F` with the explicit windowed projection
  have hstarid : (fun x : ℤ => star (F x)) = star (fun x : ℤ => ∑' m : ℤ,
      Work.KMTAreas.A4.win M (((s : ℝ) : FreqCircle)) m * g (x - m)) := by
    rw [hFdef, hwdef]
    rfl
  refine ⟨fun x => star (F x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the sup bound
    intro x
    show ‖star (F x)‖ ≤ C
    calc ‖star (F x)‖ = ‖F x‖ := norm_star _
      _ ≤ ∑' m : ℤ, ‖w m‖ := hFsup x
      _ ≤ C₀ := hwC
      _ ≤ C := hC₀C
  · -- (2) summability
    simpa only [norm_star] using hFsum
  · -- (3) the `ℓ¹` mass
    have hsum : (∑' x : ℤ, ‖star (F x)‖) = ∑' x : ℤ, ‖F x‖ := tsum_congr fun x => norm_star _
    rw [hsum]
    calc (∑' x : ℤ, ‖F x‖) ≤ C₀ * ∑' x : ℤ, ‖g x‖ :=
          hF1.trans (mul_le_mul_of_nonneg_right hwC (tsum_nonneg fun x => norm_nonneg _))
      _ ≤ C * ∑' x : ℤ, ‖g x‖ :=
          mul_le_mul_of_nonneg_right hC₀C (tsum_nonneg fun x => norm_nonneg _)
  · -- (4) the Fourier support
    intro ξ hξ
    have hneg : -ξ ∉ Work.KMTAreas.A4.arcSet ((s : ℝ) : FreqCircle) (1 / M) :=
      fun hc => hξ (Work.KMTAreas.A4.neg_mem_arcSet_iff.mp hc)
    change ZFourier (fun x : ℤ => star (F x)) ξ = 0
    rw [Work.KMTAreas.A4.ZFourier_star_flip hFsum ξ, hFZ (-ξ), hwin.1 (-ξ) hneg, zero_mul,
      star_zero]
  · -- (5) the pairing
    exact hpair
  · -- (6) the `ℓ¹` fringe
    have h1 := hFri N hN A hA N₀ hN₀le g hgbd hsupp M hM1 s
    rw [hstarid]
    exact h1.trans (mul_le_mul_of_nonneg_right hCfC hMpos.le)
  · -- (7) the `ℓ²` decay
    intro R hR
    have h1 := hDec N hN N₀ hN₀le g hgsum hgbd hsupp M hM s R hR
    rw [hstarid]
    have h2 : Cd ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree
        ≤ C ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCdpos.le hCdC 2) (by positivity)
    exact h1.trans h2

end Work.KMTAreas.A4Z
