/-
# Corollary `struct-iii` at a free window `A` (`A4.structiiiWinA`)

Krause--Mirek--Tao, §5, Corollary `struct-iii` in the window-parameterised form of
`A4/improvOneZDefs.lean`: from Proposition `propdual` at the window `A` (`PropdualAClaim P A`),
the Ionescu--Wainger multiplier theorem at even exponents (`AreaA1`) and the `ℓ^p`-improving
estimate for the linear polynomial average `A_N^{X-P}` (`PolyImproving (X - P)`), the `ℓ²` bound
for the good-`λ` error of the dual function holds with `‖g‖_{ℓ²}` on the right in place of
`‖g‖_{ℓ^∞}`.

The proof is the paper's: (a) Proposition `propdual` gives
`‖(1-Π)A*_N(h,g)‖_2 ≲ 2^{-cl}N^{d/2}‖g‖_∞`; (b) the pointwise bound
`|A*_N(h,g)(x)| ≤ A_N^{X-P}|g|(x)` together with the `ℓ^p`-improving estimate and the
`ℓ²`-boundedness of `Π` gives `‖(1-Π)A*_N(h,g)‖_2 ≲ ⟨l⟩ N^{d(1/2-1/p)}‖g‖_p`; (c) the level-set
interpolation of the two bounds, `‖g₁‖_p ≤ λ^{1-2/p}‖g‖_2^{2/p}`, gives the claim with the
exponential gain `2^{-c(1-p/2)l}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.norm_AhalfTranspose_le
import Submission.Work.KMTAreas.A5.Endpoints
import Submission.Work.KMTAreas.A4.structiiiInterpArith
import Submission.Work.KMTAreas.A4.AhalfTranspose_lp_bound
import Submission.Work.KMTAreas.A4.eLpNorm_le_of_sup_and_lp_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger (L2Z)
open Work.Analysis.IWMultiplier (angleBracket)

/-! ## Elementary algebraic facts about the dual function -/

/-- The dual function `Ã*_N(h,·)` is additive in its second argument. -/
theorem AhalfTranspose_add (N : ℕ) (P : Polynomial ℤ) (h u v : ℤ → ℂ) :
    AhalfTranspose N P h (u + v) = AhalfTranspose N P h u + AhalfTranspose N P h v := by
  funext x
  simp only [AhalfTranspose, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The dual function `Ã*_N(h,·)` is `ℂ`-homogeneous in its second argument. -/
theorem AhalfTranspose_smul (N : ℕ) (P : Polynomial ℤ) (h u : ℤ → ℂ) (c : ℂ) :
    AhalfTranspose N P h (c • u) = c • AhalfTranspose N P h u := by
  funext x
  simp only [AhalfTranspose, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ i ∈ Ioc (N / 2) N, h (x - (i:ℤ)) * (c * u (x + P.eval (i:ℤ) - (i:ℤ))))
      = c * (∑ i ∈ Ioc (N / 2) N, h (x - (i:ℤ)) * u (x + P.eval (i:ℤ) - (i:ℤ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- The dual function is bounded whenever its second argument is. -/
theorem boundedZ_AhalfTranspose (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hhb : ∀ x : ℤ, ‖h x‖ ≤ 1) (hgb : ∀ x : ℤ, ‖g x‖ ≤ M) :
    Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h g) :=
  ⟨M, fun x => by
    have h1 := norm_AhalfTranspose_le N P h g (show (0:ℝ) ≤ 1 by norm_num) hM hhb hgb x
    simpa using h1⟩

/-- `(1 - Π_{≤l,≤k})Ã*_N(h,·)` is additive in its second argument, at pairs whose dual functions
are bounded (which holds, in particular, for supported arguments). -/
theorem sub_kmtProj_AhalfTranspose_add (N : ℕ) (P : Polynomial ℤ) (h u v : ℤ → ℂ) (ρ : ℝ)
    (l : ℕ) (k : ℤ)
    (hu : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u))
    (hv : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h v)) :
    (fun x : ℤ => AhalfTranspose N P h (u + v) x
        - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h (u + v)) x)
      = (fun x : ℤ => AhalfTranspose N P h u x
            - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h u) x)
        + (fun x : ℤ => AhalfTranspose N P h v x
            - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h v) x) := by
  funext x
  rw [Pi.add_apply, AhalfTranspose_add,
    Work.KMTAreas.A5.kmtProj_add_bounded ρ l k hu hv]
  simp only [Pi.add_apply]
  ring

/-- `(1 - Π_{≤l,≤k})Ã*_N(h,·)` is `ℂ`-homogeneous in its second argument, at arguments whose dual
function is bounded. -/
theorem sub_kmtProj_AhalfTranspose_smul (N : ℕ) (P : Polynomial ℤ) (h u : ℤ → ℂ) (ρ : ℝ)
    (l : ℕ) (k : ℤ) (c : ℂ)
    (hu : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u)) :
    (fun x : ℤ => AhalfTranspose N P h (c • u) x
        - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h (c • u)) x)
      = c • (fun x : ℤ => AhalfTranspose N P h u x
            - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h u) x) := by
  funext x
  rw [AhalfTranspose_smul, Work.KMTAreas.A5.kmtProj_smul_bounded ρ l k c hu]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The sup-norm bound with a free amplitude

Proposition `propdual` is stated for `1`-bounded `g`.  Since `(1-Π)Ã*_N(h,·)` is `ℂ`-linear in
`g`, it extends to arbitrary amplitudes: if `‖g‖_∞ ≤ M` then the same bound holds with a factor
`M` on the right. -/

theorem eLpNorm_le_of_propdualAHyp {P : Polynomial ℤ} {A c ρ Cρ : ℝ} {C : ℝ≥0}
    (hpd : PropdualAHyp P A c ρ Cρ C) {N N₀ l : ℕ} {h : ℤ → ℂ}
    (hN : 1 ≤ N) (hN0lo : (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ))
    (hN0hi : (N₀ : ℝ) + (N : ℝ) ≤ A * (N : ℝ) ^ P.natDegree)
    (hhs : SupportIn h N₀) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
      ((l : ℤ) - Work.Analysis.EndVar.logN N)) :
    ∀ (g : ℤ → ℂ) (M : ℝ), 0 ≤ M → SupportIn g N₀ → (∀ x : ℤ, ‖g x‖ ≤ M) →
      MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
          - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
              (AhalfTranspose N P h g) x) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ)))
              * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ)) * M) := by
  intro g M hM0 hgs hgb
  set X : ℝ := (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ)))
      * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ)) with hXdef
  have hCnonneg : (0 : ℝ) ≤ (C : ℝ) := C.2
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg hCnonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _))
  rcases eq_or_lt_of_le hM0 with hM | hMpos
  · -- the zero amplitude
    have hg0 : g = 0 := by
      funext x
      have hx := hgb x
      rw [← hM] at hx
      exact norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
    rw [hg0]
    have hfun : (fun x : ℤ => AhalfTranspose N P h (0 : ℤ → ℂ) x
        - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
            (AhalfTranspose N P h (0 : ℤ → ℂ)) x) = 0 := by
      funext x
      have hA0 : AhalfTranspose N P h (0 : ℤ → ℂ) = 0 := by
        funext y
        simp [AhalfTranspose]
      rw [hA0, Work.KMTContract.kmtProj_zero]
      simp
    rw [hfun, MeasureTheory.eLpNorm_zero]
    have hz : (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ)))
        * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ)) * M = 0 := by rw [← hM]; ring
    rw [hz, ENNReal.ofReal_zero]
  · -- the general amplitude: rescale `g` to `1`-boundedness
    set g' : ℤ → ℂ := (M : ℂ)⁻¹ • g with hg'def
    have hgs' : SupportIn g' N₀ := by
      intro x hx
      rw [hg'def, Pi.smul_apply, hgs x hx, smul_zero]
    have hg'1 : ∀ x : ℤ, ‖g' x‖ ≤ 1 := by
      intro x
      rw [hg'def, Pi.smul_apply, norm_smul]
      have hnorm : ‖((M : ℂ)⁻¹)‖ = M⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMpos.le]
      rw [hnorm]
      calc M⁻¹ * ‖g x‖ ≤ M⁻¹ * M :=
            mul_le_mul_of_nonneg_left (hgb x) (inv_nonneg.mpr hMpos.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)
    have hbound := hpd N N₀ l g' h hN hN0lo hN0hi hgs' hhs hg'1 hh1 hgood
    have hbound' : MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g' x
          - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
              (AhalfTranspose N P h g') x) 2
          MeasureTheory.Measure.count ≤ ENNReal.ofReal X := by
      refine hbound.trans (le_of_eq ?_)
      rw [hXdef, ENNReal.coe_nnreal_eq, ENNReal.ofReal_mul hCnonneg]
    have hMg' : (M : ℂ) • g' = g := by
      rw [hg'def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hMpos), one_smul]
    have hbdd' : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h g') :=
      boundedZ_AhalfTranspose N P h g' (M := 1) (by norm_num) hh1 hg'1
    have hscale : (fun x : ℤ => AhalfTranspose N P h g x
          - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
              (AhalfTranspose N P h g) x)
        = (M : ℂ) • (fun x : ℤ => AhalfTranspose N P h g' x
            - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
                (AhalfTranspose N P h g') x) := by
      conv_lhs => rw [← hMg']
      exact sub_kmtProj_AhalfTranspose_smul N P h g' ρ l
        ((l : ℤ) - Work.Analysis.EndVar.logN N) (M : ℂ) hbdd'
    rw [hscale, MeasureTheory.eLpNorm_const_smul]
    have hnormM : ‖((M : ℂ))‖ₑ = ENNReal.ofReal M := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
    rw [hnormM]
    have hstep : ENNReal.ofReal M * MeasureTheory.eLpNorm (fun x : ℤ =>
        AhalfTranspose N P h g' x
          - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
              (AhalfTranspose N P h g') x) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (X * M) := by
      calc ENNReal.ofReal M * MeasureTheory.eLpNorm (fun x : ℤ =>
            AhalfTranspose N P h g' x
              - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
                  (AhalfTranspose N P h g') x) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal M * ENNReal.ofReal X := mul_le_mul' le_rfl hbound'
        _ = ENNReal.ofReal (X * M) := by
            rw [ENNReal.ofReal_mul hX0, mul_comm]
    refine hstep.trans (le_of_eq ?_)
    rw [hXdef]

/-! ## Boundedness from finite support -/

/-- A function supported in `[-N₀,N₀]` is bounded. -/
theorem boundedZ_of_supportIn {f : ℤ → ℂ} {N₀ : ℕ} (h : SupportIn f N₀) :
    Work.KMTAreas.A5.BoundedZ f := by
  refine ⟨∑ y ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ), ‖f y‖, fun x => ?_⟩
  by_cases hx : x ∈ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)
  · exact Finset.single_le_sum (fun i _ => norm_nonneg (f i)) hx
  · have hfx : f x = 0 := by
      by_contra hne
      exact hx (SupportIn.mem_Icc h hne)
    rw [hfx, norm_zero]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg (f i))

/-- The dual function of a supported `g` and a `1`-bounded `h` is bounded. -/
theorem boundedZ_AhalfTranspose_of_supportIn {N N₀ : ℕ} {P : Polynomial ℤ} {h u : ℤ → ℂ}
    (hu : SupportIn u N₀) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u) := by
  obtain ⟨C, hC⟩ := boundedZ_of_supportIn hu
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine ⟨C, fun x => ?_⟩
  have h1 := norm_AhalfTranspose_le N P h u (show (0:ℝ) ≤ 1 by norm_num) hC0 hh1 hC x
  simpa using h1

/-- The `(1 - Π)`-projected dual function, as a function of its second argument. -/
noncomputable def Tproj (N : ℕ) (P : Polynomial ℤ) (h : ℤ → ℂ) (ρ : ℝ) (l : ℕ) (k : ℤ)
    (u : ℤ → ℂ) : ℤ → ℂ :=
  fun x => AhalfTranspose N P h u x - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h u) x

theorem Tproj_add (N : ℕ) (P : Polynomial ℤ) (h u v : ℤ → ℂ) (ρ : ℝ) (l : ℕ) (k : ℤ)
    (hu : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u))
    (hv : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h v)) :
    Tproj N P h ρ l k (u + v) = Tproj N P h ρ l k u + Tproj N P h ρ l k v := by
  funext x
  show AhalfTranspose N P h (u + v) x
      - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h (u + v)) x
      = (AhalfTranspose N P h u x - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h u) x)
        + (AhalfTranspose N P h v x - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h v) x)
  rw [AhalfTranspose_add, Work.KMTAreas.A5.kmtProj_add_bounded ρ l k hu hv]
  simp only [Pi.add_apply]
  ring

theorem Tproj_smul (N : ℕ) (P : Polynomial ℤ) (h u : ℤ → ℂ) (ρ : ℝ) (l : ℕ) (k : ℤ) (c : ℂ)
    (hu : Work.KMTAreas.A5.BoundedZ (AhalfTranspose N P h u)) :
    Tproj N P h ρ l k (c • u) = c • Tproj N P h ρ l k u := by
  funext x
  show AhalfTranspose N P h (c • u) x
      - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h (c • u)) x
      = c * (AhalfTranspose N P h u x - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h u) x)
  rw [AhalfTranspose_smul, Work.KMTAreas.A5.kmtProj_smul_bounded ρ l k c hu]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Corollary `struct-iii` at the window `A`**: `PropdualAClaim` together with the
`ℓ^p`-improving estimate for `X - P` gives the `ℓ²` bound with `‖g‖_{ℓ²}` on the right. -/
theorem structiiiWinA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hA3 : Work.KMTContract.PolyImproving (Polynomial.X - P)) (A : ℝ) (hA : 1 ≤ A) (hProp : Work.KMTAreas.A4.PropdualAClaim P A) : Work.KMTAreas.A4.StructiiiAClaim P A := by
  classical
  obtain ⟨cA, hcApos, hPropAll⟩ := hProp
  obtain ⟨p, hp1, hp2, hBall⟩ := AhalfTranspose_lp_bound P hP hA1 hA3
  have hbpos : 0 < 1 - p / 2 := by linarith
  have hc'pos : 0 < cA * (1 - p / 2) / 2 := by positivity
  have hc'lt : cA * (1 - p / 2) / 2 < cA * (1 - p / 2) := by
    have hpos : 0 < cA * (1 - p / 2) := mul_pos hcApos hbpos
    linarith
  refine ⟨cA * (1 - p / 2) / 2, hc'pos, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨CρA, hCρApos, CA, hCApos, hpdA⟩ := hPropAll ρ hρ0 hρ1
  obtain ⟨CρB, hCρBpos, KB, hKBpos, hBρ⟩ := hBall ρ hρ0 hρ1
  set Cρ : ℝ := max CρA (max CρB 2) with hCρdef
  have hCρA_le : CρA ≤ Cρ := le_max_left _ _
  have hCρB_le : CρB ≤ Cρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2Cρ : 2 ≤ Cρ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCρpos : 0 < Cρ := lt_of_lt_of_le (by norm_num) h2Cρ
  obtain ⟨Karith, hKarithpos, hKarith⟩ :=
    Work.KMTAreas.A4.structiiiInterpArith (p := p) (a := cA)
      (c := cA * (1 - p / 2) / 2) (CA := (CA : ℝ)) (CY := KB) (d := P.natDegree)
      hp1 hp2 hcApos hc'pos hc'lt (by exact_mod_cast hCApos) hKBpos
  set Kfin : ℝ := 2 * Karith with hKfindef
  have hKfinpos : 0 < Kfin := by rw [hKfindef]; positivity
  refine ⟨Cρ, hCρpos, ⟨Kfin.toNNReal, ?_, ?_⟩⟩
  · rw [← NNReal.coe_pos, Real.coe_toNNReal _ hKfinpos.le]
    exact hKfinpos
  intro N N₀ l g h hN hN0lo hN0hi hgs hhs hgmem hh1 hgood
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  set k : ℤ := (l : ℤ) - Work.Analysis.EndVar.logN N with hkdef
  set X : ℝ := (CA : ℝ) * ((2 : ℝ) ^ (-(cA * (l : ℝ))) * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ)) with hXdef
  set Y : ℝ := KB * (max 1 (l : ℝ)) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)) with hYdef
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  have hgoodA : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρA l k :=
    Work.KMTAreas.A5.goodMajorArcs_mono hCρA_le hgood
  have hgoodB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l k :=
    Work.KMTAreas.A5.goodMajorArcs_mono hCρB_le hgood
  have hadd : ∀ u v : ℤ → ℂ, SupportIn u N₀ → SupportIn v N₀ →
      Tproj N P h ρ l k (u + v) = Tproj N P h ρ l k u + Tproj N P h ρ l k v :=
    fun u v hu hv => Tproj_add N P h u v ρ l k
      (boundedZ_AhalfTranspose_of_supportIn hu hh1)
      (boundedZ_AhalfTranspose_of_supportIn hv hh1)
  have hsup : ∀ (u : ℤ → ℂ) (M : ℝ), 0 ≤ M → SupportIn u N₀ → (∀ x : ℤ, ‖u x‖ ≤ M) →
      MeasureTheory.eLpNorm (Tproj N P h ρ l k u) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (X * M) := by
    intro u M hM0 hus huM
    have h1 := eLpNorm_le_of_propdualAHyp hpdA hN hN0lo hN0hi hhs hh1 hgoodA u M hM0 hus huM
    rw [hXdef]
    exact h1
  have hlp : ∀ u : ℤ → ℂ, MeasureTheory.eLpNorm (Tproj N P h ρ l k u) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Y * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro u
    have h1 := hBρ l k hgoodB N hN u h hh1
    rw [hYdef]
    exact h1
  have hga : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      = ENNReal.ofReal ((MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal) :=
    (ENNReal.ofReal_toReal (hgmem.eLpNorm_lt_top).ne).symm
  have hkey := eLpNorm_le_of_sup_and_lp_bound (T := Tproj N P h ρ l k) (N₀ := N₀) hadd hp1 hp2
    hXpos hYpos hsup hlp hgs ENNReal.toReal_nonneg hga
  have harith : 2 * X ^ (1 - p / 2) * Y ^ (p / 2)
      ≤ (2 * Karith) * (2 : ℝ) ^ (-((cA * (1 - p / 2) / 2) * (l : ℝ))) := by
    have h := hKarith N hN l
    have hXeq : X = (CA : ℝ) * (2 : ℝ) ^ (-(cA * (l : ℝ)))
        * (((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ)) := by rw [hXdef]; ring
    have hYeq : Y = KB * (max 1 (l : ℝ))
        * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)) := by rw [hYdef]
    rw [hXeq, hYeq]
    linarith [h]
  have hfinal : ENNReal.ofReal (2 * X ^ (1 - p / 2) * Y ^ (p / 2))
      ≤ (Kfin.toNNReal : ENNReal)
        * ENNReal.ofReal ((2 : ℝ) ^ (-((cA * (1 - p / 2) / 2) * (l : ℝ)))) := by
    have hcoeeq : ENNReal.ofReal Kfin = ((Real.toNNReal Kfin : NNReal) : ENNReal) := by
      conv_lhs => rw [← Real.coe_toNNReal Kfin hKfinpos.le]
      exact ENNReal.ofReal_coe_nnreal
    rw [← hcoeeq, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hKfindef]
    exact harith
  have hkey' : MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
        - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h g) x) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * X ^ (1 - p / 2) * Y ^ (p / 2))
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := hkey
  rw [hkdef] at hkey'
  exact hkey'.trans (mul_le_mul' hfinal le_rfl)

end Work.KMTAreas.A4
