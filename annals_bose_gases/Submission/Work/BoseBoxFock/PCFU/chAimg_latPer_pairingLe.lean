import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.coulombDual_W1_le
import Submission.Work.BoseBoxFock.PCFU.taperSlotOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary helpers for the `latPer3`-pairing bound

The target is the `H^{-1}` (Coulomb-duality) bound for the periodisation `latPer3 ℓ W₁` paired
against a smooth test function supported in one box.  The route:

* expand the periodisation `latPer3 ℓ W₁ (y−w) = ℓ³ Σ'_m W₁ (y−w+ℓm)`;
* since `W₁` is supported in the ball of radius `R ≤ chiR0·ℓ` and the lattice points are
  `ℓ`-separated, only the finitely many `m` in a fixed cube of lattice points around `y/ℓ`
  contribute, and their number is bounded by the fixed constant `(M+1)³`;
* each surviving term is `∫ W₁(u)·g(c−u)du` for `c = y+ℓm`, bounded by the Coulomb duality
  `coulombDual_W1_le` (`‖∫W₁ψ‖² ≤ 64π(a v)·Dir(ψ)`);
* the reflection `u ↦ c−u` leaves the Dirichlet energy of `g` unchanged. -/

/-- Coordinates of the lattice translate `ℓ • latVec m`. -/
private lemma ofLp_smul_latVec (ℓ : ℝ) (m : Fin 3 → ℤ) (i : Fin 3) :
    (ℓ • Work.BoseBoxFock.latVec m).ofLp i = ℓ * (m i : ℝ) := by
  rw [WithLp.ofLp_smul, Work.BoseBoxFock.latVec]
  simp

/-- Coordinates of `y + ℓ • latVec m`. -/
private lemma ofLp_add_smul_latVec (y : E3) (ℓ : ℝ) (m : Fin 3 → ℤ) (i : Fin 3) :
    (y + ℓ • Work.BoseBoxFock.latVec m).ofLp i = y.ofLp i + ℓ * (m i : ℝ) := by
  rw [WithLp.ofLp_add, Pi.add_apply, ofLp_smul_latVec]

/-- **The derivative of `u ↦ g(c−u)`** (complexified): the reflection `u ↦ c−u` contributes only
the sign. -/
private lemma fderiv_ofReal_comp_const_sub {g : E3 → ℝ} {c x : E3} {j : Fin 3}
    (hg : DifferentiableAt ℝ g (c - x)) :
    fderiv ℝ (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) x (EuclideanSpace.single j (1 : ℝ))
      = - (((fderiv ℝ g (c - x)) (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u : E3 => c - u) (-(1 : E3 →L[ℝ] E3)) x :=
    (hasFDerivAt_id x).const_sub c
  have h2 : HasFDerivAt (fun v : E3 => ((g v : ℝ) : ℂ))
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ g (c - x))) (c - x) :=
    Complex.ofRealCLM.hasFDerivAt.comp (c - x) hg.hasFDerivAt
  have h3 : fderiv ℝ (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) x =
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ g (c - x))) ∘SL (-(1 : E3 →L[ℝ] E3)) := by
    have hh := (h2.comp x h1).fderiv
    simpa only [Function.comp_def] using hh
  rw [h3]
  simp [ContinuousLinearMap.comp_apply]

/-- The reflection `u ↦ c−u` preserves the Dirichlet energy of a smooth function. -/
private lemma dirichlet_comp_const_sub {g : E3 → ℝ} {c : E3} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    (∑ j : Fin 3, ∫ x : E3, ‖(fderiv ℝ (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) x)
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∑ j : Fin 3, ∫ x : E3, ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpt : ∀ x : E3, ‖(fderiv ℝ (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) x)
      (EuclideanSpace.single j (1 : ℝ))‖
        = ‖(fderiv ℝ g (c - x)) (EuclideanSpace.single j (1 : ℝ))‖ := by
    intro x
    rw [fderiv_ofReal_comp_const_sub (hg.differentiable (by simp) (c - x))]
    simp
  calc ∫ x : E3, ‖(fderiv ℝ (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) x)
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∫ x : E3, ‖(fderiv ℝ g (c - x)) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
        simp only []
        rw [hpt x]
    _ = ∫ x : E3, ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        MeasureTheory.integral_sub_left_eq_self
          (fun x : E3 => ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume c

/-- The squared coordinate derivative of a smooth compactly supported function is integrable. -/
private lemma integrable_dirichlet_sq {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : HasCompactSupport g) (j : Fin 3) :
    Integrable (fun x : E3 => ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  set F : E3 → ℝ := fun x => (fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ)) with hF
  have hcont : Continuous F := (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsub : tsupport F ⊆ tsupport g := by
    rw [hF]
    exact tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := g) (EuclideanSpace.single j (1 : ℝ))
  have hcs : HasCompactSupport F :=
    IsCompact.of_isClosed_subset hgs.isCompact (isClosed_tsupport _) hsub
  have hint : Integrable F := hcont.integrable_of_hasCompactSupport hcs
  obtain ⟨B, hB⟩ := hgs.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  have hbdd : ∀ x : E3, ‖F x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ tsupport g
    · exact le_trans (hB x hx) (le_max_left _ _)
    · have hFx : F x = 0 := by
        by_contra hne
        exact hx (hsub (subset_tsupport F hne))
      simp [hFx]
  refine Integrable.mono' (hint.norm.const_mul (max B 0))
    ((hint.norm).aestronglyMeasurable.pow 2) (Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [hbdd x, norm_nonneg (F x)]

/-- `∫ Σ_j ‖∂_j g‖² = Σ_j ∫ ‖∂_j g‖²` for a smooth compactly supported `g`. -/
private lemma dirichlet_integral_sum {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgs : HasCompactSupport g) :
    (∫ x : E3, ∑ j : Fin 3, ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∑ j : Fin 3, ∫ x : E3, ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
  MeasureTheory.integral_finsetSum _ (fun j _ => integrable_dirichlet_sq hg hgs j)

theorem chAimg_latPer_pairingLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (y : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) g →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ →
        ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            Work.BoseBoxFock.latPer3 ℓ (Work.BoseFixR.W1fun v h ℓ) (y - w)‖
          ≤ C * Real.sqrt (BoseGases.a v) * ℓ ^ 3
              * Real.sqrt (∫ x : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
                  ‖fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  classical
  -- ## the global constants
  set K0 : ℝ := 1 / 2 + Submission.BoseGases.chiR0 with hK0def
  set M : ℕ := Nat.ceil (2 * K0) + 1 with hMdef
  refine ⟨((M : ℝ) + 1) ^ 3 * 8 * Real.sqrt Real.pi, by positivity, ?_⟩
  intro ℓ hℓ hRℓ y g hg hgs
  -- ## the weight
  set W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hWdef
  obtain ⟨hWint0, hWsupp0, _hWeven0⟩ :=
    Work.BoseBoxFock.PCFU.slotW1_aux (v := v) (h := h) (R := R) (ℓ := ℓ) hR hvrad hv_supp hℓ hRℓ
  have hWint : Integrable W := by rw [hWdef]; exact hWint0
  have hWsupp : ∀ x : E3, R ≤ ‖x‖ → W x = 0 := by
    intro x hx; rw [hWdef]; exact hWsupp0 x hx
  -- ## `a v ≥ 0`
  have ha0 : 0 ≤ BoseGases.a v := by
    have hg0nn : 0 ≤ᵐ[(volume : Measure E3)] Submission.BoseGases.g0 v h :=
      Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
    have hint := MeasureTheory.integral_nonneg_of_ae hg0nn
    rw [Submission.BoseGases.g0_integral hR hv_supp h] at hint
    nlinarith [Real.pi_pos]
  -- ## the Dirichlet energy of the test function
  set D : ℝ := ∫ x : E3, ∑ j : Fin 3, ‖(fderiv ℝ g x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
    with hDdef
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact integral_nonneg (fun x => Finset.sum_nonneg (fun _ _ => by positivity))
  -- ## geometric data
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
      (fun x hx => hgs (subset_tsupport g hx))
  have hK0pos : 0 < K0 := by rw [hK0def]; linarith [Submission.BoseGases.chiR0_pos]
  have hMge : 2 * K0 + 1 ≤ (M : ℝ) := by
    rw [hMdef]
    have h1 : 2 * K0 ≤ ((Nat.ceil (2 * K0) : ℕ) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hboxL : ∀ ⦃w : E3⦄, w ∈ Work.BoseK15.corpusBox.boxL ℓ → ∀ i : Fin 3,
      |w.ofLp i| ≤ ℓ / 2 :=
    fun w hw i => (Work.BoseBoxFock.mem_corpusBox_boxL hℓ w).mp hw i
  -- the lattice block and its complement
  set n : Fin 3 → ℤ := fun i => ⌊(-K0 - y.ofLp i / ℓ)⌋ with hndef
  have hn_le : ∀ i : Fin 3, (n i : ℝ) ≤ -K0 - y.ofLp i / ℓ := fun i => by
    rw [hndef]; exact Int.floor_le _
  have hn_lt : ∀ i : Fin 3, -K0 - y.ofLp i / ℓ < (n i : ℝ) + 1 := fun i => by
    rw [hndef]; exact Int.lt_floor_add_one _
  set S : Finset (Fin 3 → ℤ) :=
    Fintype.piFinset (fun i : Fin 3 => Finset.Icc (n i) (n i + (M : ℤ))) with hSdef
  have hScard : S.card = (M + 1) ^ 3 := by
    rw [hSdef, Fintype.card_piFinset]
    have hfac : ∀ i : Fin 3, (Finset.Icc (n i) (n i + (M : ℤ))).card = M + 1 := by
      intro i
      rw [Int.card_Icc]
      have h : (n i + (M : ℤ) + 1 - n i) = ((M : ℤ) + 1) := by ring
      rw [h, show ((M : ℤ) + 1) = ((M + 1 : ℕ) : ℤ) by push_cast; ring]
      exact Int.toNat_natCast _
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const]
    simp
  -- the complement of the block lies beyond `K0 ℓ` in norm, coordinatewise
  have hScompl : ∀ m : Fin 3 → ℤ, m ∉ S →
      ∃ i : Fin 3, K0 * ℓ < |y.ofLp i + ℓ * (m i : ℝ)| := by
    intro m hm
    have hnot : ¬ (∀ i : Fin 3, m i ∈ Finset.Icc (n i) (n i + (M : ℤ))) := by
      intro hc
      exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hc)
    rw [not_forall] at hnot
    obtain ⟨i, hi⟩ := hnot
    rw [Finset.mem_Icc] at hi
    refine ⟨i, ?_⟩
    have hkey : K0 < |y.ofLp i / ℓ + (m i : ℝ)| := by
      rcases not_and_or.mp hi with hlt | hgt
      · have hlt' : m i < n i := not_le.mp hlt
        have h1 : ((m i : ℤ) : ℝ) < (n i : ℝ) := Int.cast_lt.mpr hlt'
        have h2 : (m i : ℝ) < -K0 - y.ofLp i / ℓ := lt_of_lt_of_le h1 (hn_le i)
        have h3 : y.ofLp i / ℓ + (m i : ℝ) < -K0 := by linarith
        rw [abs_of_neg (by linarith)]
        linarith
      · have hgt' : n i + (M : ℤ) < m i := not_le.mp hgt
        have h1 : n i + (M : ℤ) + 1 ≤ m i := Int.lt_iff_add_one_le.mp hgt'
        have h2 : (n i : ℝ) + (M : ℝ) + 1 ≤ (m i : ℝ) := by
          have hcast : ((((n i + (M : ℤ) + 1 : ℤ))) : ℝ) ≤ ((m i : ℤ) : ℝ) := by
            rw [Int.cast_le]; exact h1
          push_cast at hcast
          linarith
        have h3 : y.ofLp i / ℓ + (m i : ℝ) > K0 := by linarith [hn_lt i, hMge, h2]
        rw [abs_of_pos (by linarith)]
        linarith
    have harg : ℓ * (y.ofLp i / ℓ + (m i : ℝ)) = y.ofLp i + ℓ * (m i : ℝ) := by
      field_simp
    have hmul : ℓ * K0 < ℓ * |y.ofLp i / ℓ + (m i : ℝ)| :=
      mul_lt_mul_of_pos_left hkey hℓ
    have hgoal : K0 * ℓ < |y.ofLp i + ℓ * (m i : ℝ)| := by
      have h1 : |y.ofLp i + ℓ * (m i : ℝ)| = ℓ * |y.ofLp i / ℓ + (m i : ℝ)| := by
        rw [← harg, abs_mul, abs_of_pos hℓ]
      rw [h1]
      nlinarith [hmul]
    exact hgoal
  -- the geometric core: off the block, `W` vanishes on the whole box
  have hgeom : ∀ (m : Fin 3 → ℤ) (w : E3), m ∉ S →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ → R < ‖y - w + ℓ • Work.BoseBoxFock.latVec m‖ := by
    intro m w hm hw
    obtain ⟨i, hi⟩ := hScompl m hm
    have hwi : |w.ofLp i| ≤ ℓ / 2 := hboxL hw i
    have hcoord : (y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i
        = y.ofLp i - w.ofLp i + ℓ * (m i : ℝ) := by
      simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply,
        ofLp_smul_latVec]
    have htri : |y.ofLp i + ℓ * (m i : ℝ)|
        ≤ |(y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i| + |w.ofLp i| := by
      rw [hcoord]
      have h := abs_add_le (y.ofLp i - w.ofLp i + ℓ * (m i : ℝ)) (w.ofLp i)
      have heq : y.ofLp i - w.ofLp i + ℓ * (m i : ℝ) + w.ofLp i
          = y.ofLp i + ℓ * (m i : ℝ) := by ring
      rwa [heq] at h
    have hnorm : |(y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i|
        ≤ ‖y - w + ℓ • Work.BoseBoxFock.latVec m‖ := by
      have h := PiLp.norm_apply_le (y - w + ℓ • Work.BoseBoxFock.latVec m) i
      rwa [Real.norm_eq_abs] at h
    have h1 : Submission.BoseGases.chiR0 * ℓ
        < |(y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i| := by
      have h2 : K0 * ℓ
          < |(y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i| + |w.ofLp i| :=
        lt_of_lt_of_le hi htri
      have hK : K0 * ℓ - ℓ / 2 = Submission.BoseGases.chiR0 * ℓ := by rw [hK0def]; ring
      rw [← hK]
      linarith
    calc R ≤ Submission.BoseGases.chiR0 * ℓ := by rw [mul_comm]; exact hRℓ
      _ < |(y - w + ℓ • Work.BoseBoxFock.latVec m).ofLp i| := h1
      _ ≤ ‖y - w + ℓ • Work.BoseBoxFock.latVec m‖ := hnorm
  -- ## Step 1: the pointwise expansion of the periodisation
  have hpt : ∀ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w)
      = (((ℓ ^ 3 : ℝ) : ℂ)) * ∑ m ∈ S,
          ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
    intro w
    by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ
    · have hsum : (∑' m : Fin 3 → ℤ, ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
          = ∑ m ∈ S, ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
        refine tsum_eq_sum (fun m hm => ?_)
        rw [hWsupp _ (le_of_lt (hgeom m w hm hw))]
        simp
      rw [Work.BoseBoxFock.latPer3, Work.BoseBoxFock.LatFourier.latPer, hsum]
      rw [show ((g w : ℝ) : ℂ) * ((((ℓ ^ 3 : ℝ) : ℂ))
            * (∑ m ∈ S, ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)))
          = (((ℓ ^ 3 : ℝ) : ℂ)) * (((g w : ℝ) : ℂ)
            * (∑ m ∈ S, ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))) from by ring,
        Finset.mul_sum]
    · have hgw : g w = 0 := by
        by_contra hne
        exact hw (hgs (subset_tsupport g hne))
      rw [hgw]
      simp
  -- ## the per-term integrals
  set T : (Fin 3 → ℤ) → ℂ := fun m => ∫ u : E3,
      ((W u : ℝ) : ℂ) * ((g (y + ℓ • Work.BoseBoxFock.latVec m - u) : ℝ) : ℂ) with hTdef
  -- ## Step 2: the integral identity
  have hstep1 : (∫ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w))
      = (((ℓ ^ 3 : ℝ) : ℂ)) * ∫ w : E3, ∑ m ∈ S,
          ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
    rw [show (∫ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w))
          = ∫ w : E3, (((ℓ ^ 3 : ℝ) : ℂ)) * (∑ m ∈ S,
              ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
          from integral_congr_ae (Eventually.of_forall (fun w => hpt w))]
    rw [MeasureTheory.integral_const_mul]
  -- integrability of the individual summands
  have hint : ∀ m ∈ S, Integrable (fun w : E3 =>
      ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
    intro m _
    have hgc : Continuous (fun w : E3 => ((g w : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hg.continuous
    obtain ⟨B, hB⟩ := (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    have hWc : Integrable (fun w : E3 =>
        ((W ((y + ℓ • Work.BoseBoxFock.latVec m) - w) : ℝ) : ℂ)) :=
      Integrable.ofReal (hWint.comp_sub_left (y + ℓ • Work.BoseBoxFock.latVec m))
    have hWc' : Integrable (fun w : E3 =>
        ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) :=
      hWc.congr (Eventually.of_forall (fun w => by
        simp only []
        congr 2
        abel))
    have hgbb : ∀ᵐ w : E3, ‖((g w : ℝ) : ℂ)‖ ≤ max B 0 := by
      refine Eventually.of_forall (fun w => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ
      · exact le_trans (hB w hw) (le_max_left _ _)
      · have h0 : g w = 0 := by
          by_contra hne
          exact hw (hgs (subset_tsupport g hne))
        rw [h0, abs_zero]
        exact le_max_right _ _
    exact (Integrable.mul_bdd hWc' hgc.aestronglyMeasurable hgbb).congr
      (Eventually.of_forall (fun w => by ring))
  have hstep2 : (∫ w : E3, ∑ m ∈ S,
        ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
      = ∑ m ∈ S, ∫ w : E3,
        ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) :=
    MeasureTheory.integral_finsetSum _ hint
  -- the substitution `w ↦ c − w`
  have hsubst : ∀ m : Fin 3 → ℤ,
      (∫ w : E3, ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
        = T m := by
    intro m
    rw [hTdef]
    have hF := MeasureTheory.integral_sub_left_eq_self
      (f := fun u : E3 => ((W u : ℝ) : ℂ)
        * ((g ((y + ℓ • Work.BoseBoxFock.latVec m) - u) : ℝ) : ℂ)) volume
      (y + ℓ • Work.BoseBoxFock.latVec m)
    rw [show (∫ w : E3, ((g w : ℝ) : ℂ) * ((W (y - w + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
          = ∫ w : E3, (fun u : E3 => ((W u : ℝ) : ℂ)
            * ((g ((y + ℓ • Work.BoseBoxFock.latVec m) - u) : ℝ) : ℂ))
              ((y + ℓ • Work.BoseBoxFock.latVec m) - w) from
        integral_congr_ae (Eventually.of_forall (fun w => by
          simp only []
          rw [show (y + ℓ • Work.BoseBoxFock.latVec m) - w
                = y - w + ℓ • Work.BoseBoxFock.latVec m from by abel,
              show (y + ℓ • Work.BoseBoxFock.latVec m)
                    - (y - w + ℓ • Work.BoseBoxFock.latVec m) = w from by abel]
          ring)), hF]
  have hchain1 : (∫ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w))
      = (((ℓ ^ 3 : ℝ) : ℂ)) * ∑ m ∈ S, T m := by
    rw [hstep1, hstep2]
    congr 1
    exact Finset.sum_congr rfl (fun m _ => hsubst m)
  -- ## Step 3: the per-term Coulomb bound
  have hterm : ∀ m : Fin 3 → ℤ,
      ‖T m‖ ≤ 8 * Real.sqrt (Real.pi * BoseGases.a v) * Real.sqrt D := by
    intro m
    set c : E3 := y + ℓ • Work.BoseBoxFock.latVec m with hcdef
    set ψ : E3 → ℂ := fun u => ((g (c - u) : ℝ) : ℂ) with hψdef
    have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      rw [hψdef]
      exact (Complex.ofRealCLM.contDiff.comp hg).comp (contDiff_const.sub contDiff_id)
    have hψsupp : Function.support ψ ⊆ (fun u : E3 => c - u) ''
        (Work.BoseK15.corpusBox.boxL ℓ) := by
      intro u hu
      have hgu : g (c - u) ≠ 0 := by
        rw [hψdef] at hu
        simpa using hu
      exact ⟨c - u, hgs (subset_tsupport g hgu), by abel⟩
    have hψc : HasCompactSupport ψ :=
      HasCompactSupport.of_support_subset_isCompact
        ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).image (continuous_const.sub continuous_id)) hψsupp
    have hdual := coulombDual_W1_le (v := v) (h := h) (R := R) (ℓ := ℓ)
      hR hv hvrad hv_supp hℓ hRℓ hψd hψc
    have hTm : T m = ∫ x : E3, ((Work.BoseFixR.W1fun v h ℓ x : ℝ) : ℂ) * ψ x := by
      rw [hTdef, hWdef, hψdef, hcdef]
    have henergy : (∑ j : Fin 3, ∫ x : E3, ‖(fderiv ℝ ψ x)
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) = D := by
      have hψeq : (fun u : E3 => ((g (c - u) : ℝ) : ℂ)) = ψ := hψdef.symm
      rw [← hψeq]
      rw [hDdef, dirichlet_integral_sum hg hgcs]
      exact dirichlet_comp_const_sub (g := g) (c := c) hg
    have hsq : ‖T m‖ ^ 2 ≤ 64 * Real.pi * BoseGases.a v * D := by
      rw [← hTm, henergy] at hdual
      exact hdual
    calc ‖T m‖ ≤ Real.sqrt (64 * Real.pi * BoseGases.a v * D) := Real.le_sqrt_of_sq_le hsq
      _ = 8 * Real.sqrt (Real.pi * BoseGases.a v) * Real.sqrt D := by
          rw [show 64 * Real.pi * BoseGases.a v * D
              = (64 * (Real.pi * BoseGases.a v)) * D from by ring]
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
          rw [show Real.sqrt 64 = 8 from by
            rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  -- ## Step 4: the assembly
  have hfinal : ‖∫ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w)‖
      ≤ (((M : ℝ) + 1) ^ 3 * 8 * Real.sqrt Real.pi) * Real.sqrt (BoseGases.a v) * ℓ ^ 3
          * Real.sqrt D := by
    calc ‖∫ w : E3, ((g w : ℝ) : ℂ) * Work.BoseBoxFock.latPer3 ℓ W (y - w)‖
        = ‖(((ℓ ^ 3 : ℝ) : ℂ)) * ∑ m ∈ S, T m‖ := by rw [hchain1]
      _ = ℓ ^ 3 * ‖∑ m ∈ S, T m‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ ℓ ^ 3 * ∑ m ∈ S, ‖T m‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ ℓ ^ 3 * ((S.card : ℝ) * (8 * Real.sqrt (Real.pi * BoseGases.a v) * Real.sqrt D)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (Finset.sum_le_sum (fun m (_ : m ∈ S) => hterm m)) ?_
          have hsumc : ∑ _m ∈ S, 8 * Real.sqrt (Real.pi * BoseGases.a v) * Real.sqrt D
              = (S.card : ℝ) * (8 * Real.sqrt (Real.pi * BoseGases.a v) * Real.sqrt D) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [hsumc]
      _ = (((M : ℝ) + 1) ^ 3 * 8 * Real.sqrt Real.pi) * Real.sqrt (BoseGases.a v)
            * ℓ ^ 3 * Real.sqrt D := by
          rw [hScard]
          rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
          push_cast
          ring
  rwa [hDdef] at hfinal

end Work.BoseBoxFock.PCFU
