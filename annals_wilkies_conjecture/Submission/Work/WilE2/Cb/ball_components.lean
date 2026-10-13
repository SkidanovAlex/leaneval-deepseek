/-
  Work.WilE2.Cb — `ball_components`: GV Corollary 3.3 in "Euclidean ball" form, assembled from
  the pieces of the shared E2 library.

  This is the ball statement (the bound on the number of connected components of a Pfaffian
  variety cut by a closed Euclidean ball, in hitting-set form) assembled from

  * `Work.WilE2.Ebc.tube_separation`, `Work.WilE2.Ebc.component_locally_level`,
    `Work.WilE2.Ebc.exists_regular_epsilon`, `Work.WilE2.Ebc.hits_of_count` and the bookkeeping
    module `Work.WilE2.Ebc.Poly` (all proved, in the shared E2 library);
  * `Work.WilE2.Cb.exists_generic_slope` (generic slope ⇒ non-degenerate Lagrange points),
    `Work.WilE2.Cb.exists_good_point` (each component of the tube contains a Lagrange point)
    and `Work.WilE2.Cb.good_card_le` (Khovanskii's bound for such points).

  The argument is the one of Milnor / Petrovskii–Oleinik, see `Ebc/Poly.lean` and
  `euclidean_ball_components.lean` for the detailed write-up:

  with `φ := ∑_{f ∈ g} f²` (so `φ ≥ 0`, `{φ = 0} = Zset c g`) and
  `F_ε := φ + ε(∑ᵢxᵢ² - ρ²)`, `D_ε := {F_ε ≤ 0}`, `S_ε := {F_ε = 0}`:

  * for small `ε` the components of `D_ε` separate the components of `Zset c g ∩ B̄_R`
    (`Ebc.tube_separation`),
  * for small `ε` with `0` a regular value of `F_ε` (`Ebc.exists_regular_epsilon`) every
    component of `D_ε` contains a point `z` of `S_ε` with `∇F_ε(z) ∥ (1,sl)`
    (`Cb.exists_good_point`),
  * for a generic slope `sl` (`Cb.exists_generic_slope`) those points are non-degenerate zeros
    of the square system `critPoly`, hence bounded by Khovanskii's hypothesis (`Cb.good_card_le`),
  * and the finite character principle (`Ebc.hits_of_count`) turns the count into a hitting set.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.Ebc.Poly
import Submission.Work.WilE2.Ebc.SlopeDefs
import Submission.Work.WilE2.Ebc.tube_separation
import Submission.Work.WilE2.Ebc.exists_regular_epsilon
import Submission.Work.WilE2.Ebc.component_locally_level
import Submission.Work.WilE2.Ebc.hits_of_count
import Submission.Work.WilE2.Ebc.exists_good_point
import Submission.Work.WilE2.Cb.good_card_le
import Submission.Work.WilE2.Cb.exists_generic_slope

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Classical
open WilkiesDesign WilkiesDesign.E
open scoped Topology

namespace Work.WilE2.Cb

/-! ## §1. The sum-of-squares function attached to a family of EA polynomials -/

/-- The real function `x ↦ ∑_{f ∈ g} (eaEval ch f x)²` represented by `sqSum g`. -/
def phiFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) : (Fin k → ℝ) → ℝ :=
  fun y => eaEval ch (sqSum g) y

@[simp] theorem phiFun_apply {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r))
    (y : Fin k → ℝ) : phiFun ch g y = eaEval ch (sqSum g) y := rfl

theorem phiFun_nonneg {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) :
    ∀ y : Fin k → ℝ, 0 ≤ phiFun ch g y := fun y => sqSum_nonneg ch g y

theorem phiFun_eq_zero_iff {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r))
    (y : Fin k → ℝ) : phiFun ch g y = 0 ↔ y ∈ Zset ch g := sqSum_eq_zero_iff ch g y

theorem phiFun_zero_set {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) :
    {y : Fin k → ℝ | phiFun ch g y = 0} = Zset ch g :=
  Set.ext fun y => phiFun_eq_zero_iff ch g y

theorem continuous_phiFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) :
    Continuous (phiFun ch g) := continuous_eaEval_fun ch (sqSum g)

theorem analyticOn_phiFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) :
    AnalyticOn ℝ (phiFun ch g) Set.univ := analyticOn_eaEval_fun ch (sqSum g)

/-- `tubeF` is the tube function of `phiFun`. -/
theorem tubeF_eq_phiFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    tubeF ch g ε ρ = tubeFun (phiFun ch g) ρ ε := tubeF_eq_tubeFun ch g ε ρ

/-- `eball` depends only on `ρ²`. -/
theorem eball_sq_eq {k : ℕ} {ρ ρ' : ℝ} (h : ρ ^ 2 = ρ' ^ 2) : eball k ρ = eball k ρ' := by
  ext y
  simp only [mem_eball, h]

/-! ## §2. A set with at most one point is hit by at most one point -/

theorem exists_hits_card_le_one {k : ℕ} {X : Set (Fin k → ℝ)} (hX : X.Subsingleton) :
    ∃ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ X ∧ s.card ≤ 1 ∧ Hits X s := by
  by_cases hne : X.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨{x₀}, ?h1, ?h2, ?h3⟩
    · intro y hy
      have hy' : y = x₀ := by simpa using hy
      simpa [hy'] using hx₀
    · simp
    · intro x hx
      refine ⟨x₀, Finset.mem_singleton_self x₀, ?_⟩
      rw [hX hx hx₀]
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x hx
    exact absurd ⟨x, hx⟩ hne

/-! ## §3. The counting lemma: `N` points in distinct components are bounded by the
Khovanskii bound -/

/-- **The tube counting lemma.**  Let `q` be a Khovanskii bound for square EA systems of format
`≤ F` (the polynomial supplied by `KhoBound F`).  Then any `N` points of `Zset ch g ∩ B̄_R` lying
in pairwise distinct components of that set satisfy
`N ≤ q.eval ((ebcDegPoly F).eval (∑ f ∈ g, atomDeg f))`. -/
theorem fin_card_le_of_components {k r F : ℕ} (q : Polynomial ℕ)
    (hq : ∀ (k' r' : ℕ) (c : EAChain k' r') (f : Fin k' → EAPoly k' r')
        (s : Finset (Fin k' → ℝ)), k' + r' ≤ F →
      (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ q.eval (∑ i, atomDeg (f i)))
    (hkr : k + r ≤ F) (hSard : SardDense) (ch : EAChain k r) (g : Finset (EAPoly k r))
    (hk : 0 < k) {R : ℝ} (hR : R ≠ 0) {N : ℕ} (x : Fin N → Fin k → ℝ)
    (hx : ∀ i, x i ∈ Zset ch g ∩ eball k R)
    (hsep : ∀ i j, i ≠ j →
      connectedComponentIn (Zset ch g ∩ eball k R) (x i)
        ≠ connectedComponentIn (Zset ch g ∩ eball k R) (x j)) :
    N ≤ q.eval ((ebcDegPoly F).eval (∑ f ∈ g, atomDeg f)) := by
  have hρpos : 0 < |R| := abs_pos.mpr hR
  have hxZ' : ∀ i, phiFun ch g (x i) = 0 :=
    fun i => (phiFun_eq_zero_iff ch g (x i)).mpr (hx i).1
  have hxb' : ∀ i, ∑ j, (x i j) ^ 2 ≤ |R| ^ 2 :=
    fun i => by rw [sq_abs]; exact (hx i).2
  have hsep' : ∀ i j, i ≠ j →
      connectedComponentIn ({y : Fin k → ℝ | phiFun ch g y = 0} ∩ eball k |R|) (x i)
        ≠ connectedComponentIn ({y : Fin k → ℝ | phiFun ch g y = 0} ∩ eball k |R|) (x j) := by
    intro i j hij
    have h := hsep i j hij
    rw [← phiFun_zero_set ch g, (eball_sq_eq (ρ := |R|) (ρ' := R) (sq_abs R)).symm] at h
    exact h
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    Ebc.tube_separation (phiFun ch g) (continuous_phiFun ch g) (phiFun_nonneg ch g) |R|
      x hxZ' hxb' hsep'
  obtain ⟨ε, hεpos, hεlt, hεreg⟩ :=
    Ebc.exists_regular_epsilon (phiFun ch g) (analyticOn_phiFun ch g) (phiFun_nonneg ch g)
      |R| hρpos hSard hε₀pos
  have hxT : ∀ i, x i ∈ tubeSet (phiFun ch g) |R| ε :=
    fun i => Ebc.mem_tubeSet_of_zero (hxZ' i) (hxb' i) (le_of_lt hεpos)
  have hFf2 : ContDiff ℝ 2 (tubeFun (phiFun ch g) |R| ε) := contDiff_tubeFun ch g ε |R|
  have hFf1 : ContDiff ℝ 1 (tubeFun (phiFun ch g) |R| ε) := hFf2.of_le (by norm_num)
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨sl, -, hsl⟩ :=
    exists_generic_slope (tubeFun (phiFun ch g) |R| ε) hFf2 hεreg i₀ 0 hεpos
  -- one Lagrange witness per point, lying in the tube component of that point
  choose z hzK hzP using fun i =>
    Ebc.exists_good_point hk (phiFun ch g) (continuous_phiFun ch g) (phiFun_nonneg ch g)
      hεpos hεreg hFf1 i₀ sl (hxT i)
  -- distinct tube components force distinct witnesses
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have h1 : IsPreconnected
        (connectedComponentIn (tubeSet (phiFun ch g) |R| ε) (x i)
          ∪ connectedComponentIn (tubeSet (phiFun ch g) |R| ε) (x j)) :=
      IsPreconnected.union' ⟨z i, hzK i, hij ▸ hzK j⟩
        isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn
    have h2 : connectedComponentIn (tubeSet (phiFun ch g) |R| ε) (x i)
        ∪ connectedComponentIn (tubeSet (phiFun ch g) |R| ε) (x j)
          ⊆ connectedComponentIn (tubeSet (phiFun ch g) |R| ε) (x i) :=
      h1.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn (hxT i)))
        (Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
    exact hε₀ ε hεpos hεlt i j hne
      (h2 (Or.inr (mem_connectedComponentIn (hxT j))))
  -- the witnesses are non-degenerate solutions of the critical system
  have hsl' : ∀ w : Fin k → ℝ, tubeF ch g ε |R| w = 0 →
      (∀ j : Fin k, j ≠ i₀ → Ebc.pderiv (tubeF ch g ε |R|) j w
        = sl j * Ebc.pderiv (tubeF ch g ε |R|) i₀ w) →
      Ebc.pderiv (tubeF ch g ε |R|) i₀ w ≠ 0 →
      ∀ v : Fin k → ℝ, v ≠ 0 → fderiv ℝ (tubeF ch g ε |R|) w v = 0 →
        ∃ j : Fin k, j ≠ i₀ ∧
          fderiv ℝ (fun w' => Ebc.pderiv (tubeF ch g ε |R|) j w'
            - sl j * Ebc.pderiv (tubeF ch g ε |R|) i₀ w') w v ≠ 0 := by
    intro w hw0 hslope hwne v hv0 hv
    have hw0' : tubeFun (phiFun ch g) |R| ε w = 0 := by
      rwa [← tubeF_eq_phiFun ch g ε |R|]
    have hslope' : ∀ j : Fin k, j ≠ i₀ →
        fderiv ℝ (tubeFun (phiFun ch g) |R| ε) w (Pi.single j 1)
          = sl j * fderiv ℝ (tubeFun (phiFun ch g) |R| ε) w (Pi.single i₀ 1) := by
      intro j hj
      have := hslope j hj
      simpa only [tubeF_eq_phiFun ch g ε |R|, Ebc.pderiv_apply] using this
    have hwne' : fderiv ℝ (tubeFun (phiFun ch g) |R| ε) w (Pi.single i₀ 1) ≠ 0 := by
      have := hwne
      simpa only [tubeF_eq_phiFun ch g ε |R|, Ebc.pderiv_apply] using this
    have hv' : fderiv ℝ (tubeFun (phiFun ch g) |R| ε) w v = 0 := by
      rwa [← tubeF_eq_phiFun ch g ε |R|]
    obtain ⟨j, hj, hjd⟩ := hsl w hw0' hslope' hwne' v hv0 hv'
    exact ⟨j, hj, by simpa only [tubeF_eq_phiFun ch g ε |R|, Ebc.pderiv_apply] using hjd⟩
  have hgood : ∀ i, z i ∈ {w : Fin k → ℝ |
      tubeF ch g ε |R| w = 0 ∧
        (∀ j : Fin k, j ≠ i₀ → Ebc.pderiv (tubeF ch g ε |R|) j w
          = sl j * Ebc.pderiv (tubeF ch g ε |R|) i₀ w) ∧
        Ebc.pderiv (tubeF ch g ε |R|) i₀ w ≠ 0} := by
    intro i
    obtain ⟨h0, hslope, hne⟩ := hzP i
    refine ⟨?_, ?_, ?_⟩
    · rw [tubeF_eq_phiFun ch g ε |R|]; exact h0
    · intro j hj
      have := hslope j hj
      simpa only [tubeF_eq_phiFun ch g ε |R|, Ebc.pderiv_apply] using this
    · have := hne
      simpa only [tubeF_eq_phiFun ch g ε |R|, Ebc.pderiv_apply] using this
  have hsub : (↑(Finset.univ.image z) : Set (Fin k → ℝ)) ⊆ {w : Fin k → ℝ |
      tubeF ch g ε |R| w = 0 ∧
        (∀ j : Fin k, j ≠ i₀ → Ebc.pderiv (tubeF ch g ε |R|) j w
          = sl j * Ebc.pderiv (tubeF ch g ε |R|) i₀ w) ∧
        Ebc.pderiv (tubeF ch g ε |R|) i₀ w ≠ 0} := by
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨i, hi⟩ := hw
    rw [← hi]
    exact hgood i
  have hbound := good_card_le q hq hkr ch g ε |R| i₀ sl hsl'
    (Finset.univ.image z) hsub
  have hcard : (Finset.univ.image z).card = N := by
    rw [Finset.card_image_of_injective _ hzinj, Finset.card_univ, Fintype.card_fin]
  rwa [hcard] at hbound

/-! ## §4. The ball statement -/

theorem ball_components (hE2a : Work.WilE2.KhoBound) (hSard : Work.WilE2.SardDense) (F : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (g : Finset (WilkiesDesign.E.EAPoly k r)) (R : ℝ),
      k + r ≤ F → ∃ s : Finset (Fin k → ℝ),
        (↑s : Set (Fin k → ℝ)) ⊆ Work.WilE2.Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2} ∧
        s.card ≤ p.eval (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ∧
        Work.WilE2.Hits (Work.WilE2.Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2}) s := by
  obtain ⟨q, hq⟩ := hE2a F
  refine ⟨q.comp (ebcDegPoly F) + 1, ?_⟩
  intro k r c g R hkr
  set D : ℕ := ∑ f ∈ g, atomDeg f with hDdef
  set M : ℕ := q.eval ((ebcDegPoly F).eval D) with hMdef
  have hpval : (q.comp (ebcDegPoly F) + 1).eval D = M + 1 := by
    simp only [hMdef, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
  -- degenerate case: `R = 0`, so the set is contained in `{0}`
  rcases eq_or_ne R 0 with hR0 | hR0
  · have hsub : (Zset c g ∩ eball k R).Subsingleton := by
      rw [hR0, eball_zero]
      intro y hy y' hy'
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hy hy'
      exact hy.2.trans hy'.2.symm
    obtain ⟨s, hsX, hscard, hsHits⟩ := exists_hits_card_le_one hsub
    exact ⟨s, hsX, by rw [hpval]; omega, hsHits⟩
  -- degenerate case: `k = 0`, so `Fin k → ℝ` is a single point
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · have hsub : (Zset c g ∩ eball k R).Subsingleton := by
      subst hk0
      intro y hy y' hy'
      funext i
      exact Fin.elim0 i
    obtain ⟨s, hsX, hscard, hsHits⟩ := exists_hits_card_le_one hsub
    exact ⟨s, hsX, by rw [hpval]; omega, hsHits⟩
  -- main case
  have hcount : ∀ t : Finset (Fin k → ℝ), (↑t : Set (Fin k → ℝ)) ⊆ Zset c g ∩ eball k R →
      (∀ i ∈ t, ∀ j ∈ t, i ≠ j →
        connectedComponentIn (Zset c g ∩ eball k R) i
          ≠ connectedComponentIn (Zset c g ∩ eball k R) j) → t.card ≤ M := by
    intro t ht htp
    let xf : Fin t.card → Fin k → ℝ := fun i => ((Finset.equivFin t).symm i).1
    have hxmem : ∀ i, xf i ∈ t := fun i => ((Finset.equivFin t).symm i).2
    have hxinj : Function.Injective xf := by
      intro i j hij
      have h1 : (Finset.equivFin t).symm i = (Finset.equivFin t).symm j := Subtype.ext hij
      exact (Finset.equivFin t).symm.injective h1
    have hstep := fin_card_le_of_components q hq hkr hSard c g hk0 hR0 xf
      (fun i => ht (hxmem i))
      (fun i j hij => htp (xf i) (hxmem i) (xf j) (hxmem j)
        (fun hh => hij (hxinj hh)))
    rw [hMdef]
    exact hstep
  obtain ⟨A, hAcard, hA, hcov⟩ := Ebc.hits_of_count hcount
  have hcb : CoverBound (Zset c g ∩ eball k R) A.card := ⟨A, le_rfl, hA, hcov⟩
  obtain ⟨s, hsX, hscard, hsHits⟩ := coverBound_hits hcb
  exact ⟨s, hsX, by rw [hpval]; omega, hsHits⟩

end Work.WilE2.Cb
