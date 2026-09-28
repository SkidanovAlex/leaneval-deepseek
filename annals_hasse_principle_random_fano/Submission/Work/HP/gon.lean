import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.gcd_sum
import Submission.Work.HP.phiOf_injective
import Submission.Work.HP.Sig2.Recursion
import Submission.Work.HP.exists_short_basis
import Submission.Work.HP.latCovol_comp_basis
import Submission.Work.HP.MDEstimates.latBallSandwichGon
import Submission.Work.HP.MDEstimates.latBallVolumeGon

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset Filter MeasureTheory
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Inner products of coefficient vectors -/

theorem gon_inner_toLp (f g : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 f) (WithLp.toLp 2 g) = ∑ k, f k * g k := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, RCLike.inner_apply]
    simpa using mul_comm (g k) (f k)

/-! ## Transport between a submodule of `ℤ^ι` and its coefficient presentation -/

variable {L : Submodule ℤ (ι → ℤ)} {R : ℕ}

/-- The underlying integer vectors of a `ℤ`-basis of `L`. -/
def vb (b : Module.Basis (Fin R) ℤ L) (i : Fin R) : ι → ℤ := (b i : ι → ℤ)

/-- The `ℤ`-linear map `t ↦ Σ i, t i • b i` from coefficients to `ℤ^ι`. -/
noncomputable def latEmb (b : Module.Basis (Fin R) ℤ L) : (Fin R → ℤ) →ₗ[ℤ] (ι → ℤ) :=
  (Submodule.subtype L).comp b.equivFun.symm.toLinearMap

theorem latEmb_apply (b : Module.Basis (Fin R) ℤ L) (t : Fin R → ℤ) :
    latEmb b t = ∑ i, t i • vb b i := by
  show ((b.equivFun.symm t : L) : ι → ℤ) = _
  rw [Module.Basis.equivFun_symm_apply]
  exact (map_sum (Submodule.subtype L) (fun i => t i • b i) Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => by rw [map_smul, vb, Submodule.coe_subtype])

theorem latEmb_equivFun (b : Module.Basis (Fin R) ℤ L) (x : L) :
    latEmb b (b.equivFun x) = (x : ι → ℤ) := by
  show ((b.equivFun.symm (b.equivFun x) : L) : ι → ℤ) = (x : ι → ℤ)
  rw [LinearEquiv.symm_apply_apply]

theorem latEmb_injective (b : Module.Basis (Fin R) ℤ L) : Function.Injective (latEmb b) := by
  intro x y h
  exact b.equivFun.symm.injective (Subtype.coe_injective h)

theorem latEmb_norm (b : Module.Basis (Fin R) ℤ L) (t : Fin R → ℤ) :
    ‖phiOf (vb b) (fun i => (t i : ℝ))‖ = eNorm (latEmb b t) := by
  rw [latEmb_apply, phiOf_norm]

/-- `ballCount` for `L` equals the coefficient-space count for the coefficient map. -/
theorem ballCount_eq_latCount (b : Module.Basis (Fin R) ℤ L) (T : ℝ) :
    ballCount L T = latCount (phiOf (vb b)) T := by
  rw [ballCount, latCount, latSet]
  refine (Set.ncard_congr (fun t _ => latEmb b t) ?_ ?_ ?_).symm
  · intro t ht
    refine ⟨(b.equivFun.symm t : L).2, ?_⟩
    have ht' : ‖phiOf (vb b) (fun i => (t i : ℝ))‖ ≤ T := ht
    rw [latEmb_norm b t] at ht'
    exact ht'
  · intro t t' _ _ h
    exact latEmb_injective b h
  · intro v hv
    obtain ⟨hvL, hvT⟩ := hv
    refine ⟨b.equivFun ⟨v, hvL⟩, ?_, latEmb_equivFun b ⟨v, hvL⟩⟩
    change ‖phiOf (vb b) (fun i => ((b.equivFun ⟨v, hvL⟩) i : ℝ))‖ ≤ T
    rw [latEmb_norm b (b.equivFun ⟨v, hvL⟩), latEmb_equivFun]
    exact hvT

/-- The successive minima of `L` are the successive minima of the coefficient lattice. -/
theorem lam_eq_latMin (b : Module.Basis (Fin R) ℤ L) (i : ℕ) :
    lam L i = latMin (phiOf (vb b)) i := by
  rw [lam, latMin]
  congr 1
  ext r
  constructor
  · rintro ⟨hr, f, hfL, hfind, hfr⟩
    set g : Fin i → (Fin R → ℤ) := fun j => b.equivFun ⟨f j, hfL j⟩ with hg
    have hcomp : (latEmb b) ∘ g = f := by
      funext j
      rw [Function.comp_apply, hg, latEmb_equivFun]
    refine ⟨hr, g, ?_, fun j => ?_⟩
    · refine LinearIndependent.of_comp (latEmb b) ?_
      rw [hcomp]; exact hfind
    · rw [latEmb_norm b (g j), hg, latEmb_equivFun]
      exact hfr j
  · rintro ⟨hr, g, hgind, hgr⟩
    refine ⟨hr, (fun j => latEmb b (g j)), fun j => (b.equivFun.symm (g j) : L).2,
      ?_, fun j => ?_⟩
    · exact LinearIndependent.map' hgind (latEmb b)
        (LinearMap.ker_eq_bot.mpr (latEmb_injective b))
    · rw [← latEmb_norm b (g j)]
      exact hgr j

theorem phiOf_single {R : ℕ} (v : Fin R → (ι → ℤ)) (i : Fin R) :
    phiOf v (Pi.single i (1:ℝ)) = WithLp.toLp 2 (fun k => ((v i) k : ℝ)) := by
  rw [← WithLp.toLp_ofLp (p := 2) (phiOf v (Pi.single i (1:ℝ)))]
  congr 1
  funext k
  rw [WithLp.ofLp_toLp, phiOf_apply]
  simp [Pi.single_apply]

/-- `detL` of `L` is the covolume of the coefficient presentation, for the canonical basis
used in the definition of `detL`. -/
theorem detL_eq_latCovol :
    detL L = latCovol (phiOf (vb (L := L)
      (b := (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2))) := by
  rw [detL, latCovol]
  congr 1
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply]
  rw [Pi.basisFun_apply, Pi.basisFun_apply, phiOf_single, phiOf_single, gon_inner_toLp]
  simp [vb]



/-! ## The cube comparison in an arbitrary coefficient basis -/

/-- The two-sided comparison of the lattice point count with the volume of the `Φ`-ball, where the
correction term is the sum of the norms of the images of the vectors of an arbitrary `ℤ`-basis `e`
of the coefficient lattice.  This is `MDEstimates.latBallSandwichGon` transported along the change
of basis `e`: the standard basis is replaced by the columns of `e`. -/
theorem gon_cube {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    (e : Module.Basis (Fin R) ℤ (Fin R → ℤ)) :
    (∀ T : ℝ, 0 ≤ T → (latCount Φ T : ℝ) ≤
        ballVol R * (T + ∑ i, ‖Φ (fun k => ((e i) k : ℝ))‖) ^ R / latCovol Φ) ∧
    (∀ T : ℝ, (∑ i, ‖Φ (fun k => ((e i) k : ℝ))‖) ≤ T →
        ballVol R * (T - ∑ i, ‖Φ (fun k => ((e i) k : ℝ))‖) ^ R / latCovol Φ
          ≤ (latCount Φ T : ℝ)) := by
  classical
  set A : Matrix (Fin R) (Fin R) ℝ := Matrix.of (fun j i : Fin R => ((e i) j : ℝ)) with hA
  set Ψ : LatMap (ι := ι) R := Φ.comp (Matrix.mulVecLin A) with hΨ
  set D : ℝ := ∑ i, ‖Φ (fun k => ((e i) k : ℝ))‖ with hD
  have hDnn : 0 ≤ D := by
    rw [hD]; exact Finset.sum_nonneg fun i _ => norm_nonneg _
  -- the change of basis is injective, via the `phiOf` presentation of the lattice `ℤ^R`
  have hMe : ∀ x : Fin R → ℝ, Matrix.mulVecLin A x
      = (phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) x).ofLp := by
    intro x
    funext j
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply, phiOf_apply]
    simp only [hA]
    simp [dotProduct]
  have hMeinj : Function.Injective (Matrix.mulVecLin A) := by
    intro x y hxy
    have h2 : (phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) x).ofLp
        = (phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) y).ofLp := by
      rw [← hMe x, ← hMe y, hxy]
    have h3 : phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) x
        = phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) y := by
      rw [← WithLp.toLp_ofLp (p := 2) (phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) x),
          ← WithLp.toLp_ofLp (p := 2) (phiOf (v := fun i : Fin R => (e i : Fin R → ℤ)) y),
          h2]
    exact phiOf_injective _ e.linearIndependent h3
  have hΨinj : Function.Injective Ψ := by
    rw [hΨ]; exact hΦ.comp hMeinj
  -- the transported coefficient map is `t ↦ e.equivFun.symm t` on integer vectors
  have hkey : ∀ t : Fin R → ℤ, Ψ (fun i => (t i : ℝ))
      = Φ (fun i => ((e.equivFun.symm t) i : ℝ)) := by
    intro t
    show Φ (Matrix.mulVecLin A (fun i => (t i : ℝ))) = _
    rw [hMe]
    congr 1
    funext k
    rw [phiOf_cast, Module.Basis.equivFun_symm_apply]
  have hcount : ∀ T : ℝ, latCount Ψ T = latCount Φ T := by
    intro T
    rw [latCount, latSet]
    refine Set.ncard_congr (fun t _ => e.equivFun.symm t) ?_ ?_ ?_
    · intro t ht
      show ‖Φ (fun i => ((e.equivFun.symm t) i : ℝ))‖ ≤ T
      rw [← hkey t]; exact ht
    · intro t t' _ _ h
      exact e.equivFun.symm.injective h
    · intro s hs
      refine ⟨e.equivFun s, ?_, e.equivFun.symm_apply_apply s⟩
      show ‖Ψ (fun i => ((e.equivFun s) i : ℝ))‖ ≤ T
      rw [hkey (e.equivFun s), e.equivFun.symm_apply_apply]
      exact hs
  have hcov : latCovol Ψ = latCovol Φ := by
    rw [hΨ, hA]
    exact latCovol_comp_basis e Φ
  have hrow : ∀ i : Fin R, Matrix.mulVecLin A (Pi.basisFun ℝ (Fin R) i)
      = fun j => ((e i) j : ℝ) := by
    intro i
    rw [Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec_single_one]
    funext j
    simp [hA, Matrix.col]
  have hsum : ∑ i, ‖Ψ (Pi.basisFun ℝ (Fin R) i)‖ = D := by
    rw [hD]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΨ]
    show ‖Φ (Matrix.mulVecLin A (Pi.basisFun ℝ (Fin R) i))‖ = ‖Φ (fun k => ((e i) k : ℝ))‖
    rw [hrow i]
  have hmu : (1 / 2) * ∑ i, ‖Ψ (Pi.basisFun ℝ (Fin R) i)‖ ≤ D := by
    rw [hsum]; linarith
  have hvol : ∀ S : ℝ, 0 ≤ S → (volume {x : Fin R → ℝ | ‖Ψ x‖ ≤ S}).toReal
      = ballVol R * S ^ R / latCovol Ψ := by
    intro S hS
    rw [MDEstimates.latBallVolumeGon hR Ψ hΨinj S hS]
    exact ENNReal.toReal_ofReal (div_nonneg
      (mul_nonneg (by rw [ballVol]; exact ENNReal.toReal_nonneg) (pow_nonneg hS R))
      (Real.sqrt_nonneg _))
  constructor
  · intro T hT
    calc (latCount Φ T : ℝ) = (latCount Ψ T : ℝ) := by rw [hcount T]
      _ ≤ (volume {x : Fin R → ℝ | ‖Ψ x‖ ≤ T + D}).toReal :=
          (MDEstimates.latBallSandwichGon Ψ hΨinj T D hT hmu).1
      _ = ballVol R * (T + D) ^ R / latCovol Ψ := hvol (T + D) (by linarith)
      _ = ballVol R * (T + D) ^ R / latCovol Φ := by rw [hcov]
  · intro T hDT
    have hT : 0 ≤ T := le_trans hDnn hDT
    calc ballVol R * (T - D) ^ R / latCovol Φ
        = ballVol R * (T - D) ^ R / latCovol Ψ := by rw [hcov]
      _ = (volume {x : Fin R → ℝ | ‖Ψ x‖ ≤ T - D}).toReal := (hvol (T - D) (by linarith)).symm
      _ ≤ (latCount Ψ T : ℝ) :=
          (MDEstimates.latBallSandwichGon Ψ hΨinj T D hT hmu).2
      _ = (latCount Φ T : ℝ) := by rw [hcount T]

def gonPP {R : ℕ} (Φ : LatMap (ι := ι) R) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, latMin Φ (j + 1)

lemma gonPP_succ {R : ℕ} (Φ : LatMap (ι := ι) R) (k : ℕ) :
    gonPP Φ (k+1) = gonPP Φ k * latMin Φ (k+1) := by
  simp [gonPP, Finset.prod_range_succ]

lemma gonPP_shift {R : ℕ} (Φ : LatMap (ι := ι) R) (k : ℕ) :
    gonPP Φ (k+1) = (∏ j ∈ Finset.range k, latMin Φ (j + 2)) * latMin Φ 1 := by
  rw [gonPP, Finset.prod_range_succ']

lemma gon_latMin_set_nonempty {R : ℕ} (Φ : LatMap (ι := ι) R) {j : ℕ} (hj : j ≤ R) :
    ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r}).Nonempty := by
  set g : Fin j → ℝ := fun l => ‖Φ (fun i => (((Pi.basisFun ℤ (Fin R)) (Fin.castLE hj l)) i : ℝ))‖
  have hg : ∀ l, 0 ≤ g l := fun l => norm_nonneg _
  refine ⟨∑ l, g l, Finset.sum_nonneg (fun l _ => hg l),
    (fun k => (Pi.basisFun ℤ (Fin R)) (Fin.castLE hj k)), ?_, fun k => ?_⟩
  · exact LinearIndependent.comp (Pi.basisFun ℤ (Fin R)).linearIndependent
      (Fin.castLE hj) (Fin.castLE_injective hj)
  · exact Finset.single_le_sum (fun l _ => hg l) (Finset.mem_univ k)

lemma gon_latMin_mono {R : ℕ} (Φ : LatMap (ι := ι) R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R) :
    latMin Φ i ≤ latMin Φ j := by
  rw [latMin, latMin]
  refine csInf_le_csInf (t := {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r})
    ⟨0, fun r hr => hr.1⟩ (gon_latMin_set_nonempty Φ hj) ?_
  rintro r ⟨hr0, f, hfind, hfr⟩
  exact ⟨hr0, fun k => f (Fin.castLE hij k),
    hfind.comp (Fin.castLE hij) (Fin.castLE_injective hij), fun k => hfr _⟩

lemma gon_latMin_pos {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) {j : ℕ}
    (h1 : 1 ≤ j) (hj : j ≤ R) : 0 < latMin Φ j := by
  obtain ⟨u, hu0, hup, hu⟩ := lat_min_attained (le_trans h1 hj) Φ hΦ
  have hpos1 : 0 < latMin Φ 1 := by
    rw [← hu, norm_pos_iff]
    intro h
    have h0 : (fun i => (u i : ℝ)) = 0 := hΦ (by rw [h, map_zero])
    exact hu0 (funext fun i => by
      have h2 : ((u i : ℤ) : ℝ) = 0 := congrFun h0 i
      exact_mod_cast h2)
  exact lt_of_lt_of_le hpos1 (gon_latMin_mono Φ h1 hj)

lemma gonPP_pos {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) {k : ℕ} (hk : k ≤ R) :
    0 < gonPP Φ k := by
  rw [gonPP]
  refine Finset.prod_pos fun j hj => ?_
  exact gon_latMin_pos Φ hΦ (Nat.succ_le_succ (Nat.zero_le j)) (by have := Finset.mem_range.mp hj; omega)


theorem gon_latCount_upper (R : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Φ : LatMap (ι := ι) R), Function.Injective Φ → ∀ T : ℝ, 1 ≤ T →
      (latCount Φ T : ℝ) ≤ K * ∑ k ∈ Finset.range (R + 1), T ^ k / gonPP Φ k := by
  induction R with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro Φ hΦ T hT
      have hcard : latCount Φ T = 1 := by
        rw [latCount, latSet]
        have huniv : {t : Fin 0 → ℤ | ‖Φ (fun i => (t i : ℝ))‖ ≤ T} = Set.univ := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          have h0 : (fun i => (t i : ℝ)) = 0 := funext fun i => Fin.elim0 i
          rw [h0, map_zero, norm_zero]
          linarith
        rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
        simp
      rw [hcard]
      have hsum : ∑ k ∈ Finset.range (0 + 1), T ^ k / gonPP Φ k = 1 := by
        rw [Finset.sum_range_one, gonPP]
        simp
      rw [hsum]
      simp
  | succ n ih =>
      obtain ⟨K, hKpos, hK⟩ := ih
      refine ⟨K * 2 ^ (n + 2), by positivity, ?_⟩
      intro Φ hΦ T hT
      have hR : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      obtain ⟨u, hu0, hup, hu⟩ := lat_min_attained hR Φ hΦ
      obtain ⟨Ψ, hΨinj, hcnt, hmin⟩ := Sig2Rec.recursion hR Φ hΦ u hu0 hup hu
      have hΛpos : 0 < latMin Φ 1 := gon_latMin_pos Φ hΦ le_rfl hR
      have hfac : 0 ≤ 2 * T / latMin Φ 1 + 1 := by
        have h1 : 0 ≤ 2 * T / latMin Φ 1 := div_nonneg (by positivity) hΛpos.le
        linarith
      have hstep : (latCount Φ T : ℝ) ≤
          (2 * T / latMin Φ 1 + 1) * (K * ∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k) := by
        have h1 : (latCount Φ T : ℝ) ≤ (2 * T / latMin Φ 1 + 1) * (latCount Ψ T : ℝ) := by
          have hh := hcnt T (by linarith)
          rwa [hu] at hh
        have h2 : (latCount Ψ T : ℝ) ≤ K * ∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k :=
          hK Ψ hΨinj T hT
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hfac)
      have hkey : (2 * T / latMin Φ 1 + 1) * (∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k)
          ≤ 2 ^ (n + 2) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by
        have hi : ∀ k, k < n + 1 →
            T ^ k / gonPP Ψ k ≤ 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1) := by
          intro k hk
          set ck : ℝ := ∏ j ∈ Finset.range k, latMin Φ (j + 2) with hck
          have hck_pos : 0 < ck := by
            rw [hck]
            refine Finset.prod_pos fun j hj => ?_
            exact gon_latMin_pos Φ hΦ (by omega) (by have := Finset.mem_range.mp hj; omega)
          have hPsi : ck / 2 ^ k ≤ gonPP Ψ k := by
            have h1 : ck / 2 ^ k = ∏ j ∈ Finset.range k, (latMin Φ (j + 2) / 2) := by
              rw [hck, Finset.prod_div_distrib]
              simp [Finset.prod_const, Finset.card_range]
            rw [h1]
            exact Finset.prod_le_prod₀
              (fun j hj => div_nonneg (gon_latMin_pos Φ hΦ (by omega)
                (by have := Finset.mem_range.mp hj; omega)).le (by norm_num))
              (fun j _ => hmin (j + 1) (by omega))
          have hPsi_pos : 0 < gonPP Ψ k :=
            lt_of_lt_of_le (div_pos hck_pos (by positivity)) hPsi
          have hPP1 : gonPP Φ (k + 1) = ck * latMin Φ 1 := by rw [hck]; exact gonPP_shift Φ k
          have hgoal : 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1) = 2 ^ k * T ^ k / ck := by
            rw [hPP1]
            field_simp
          rw [hgoal]
          calc T ^ k / gonPP Ψ k ≤ T ^ k / (ck / 2 ^ k) :=
                div_le_div_of_nonneg_left (pow_nonneg (by linarith : (0:ℝ) ≤ T) k)
                  (div_pos hck_pos (by positivity)) hPsi
            _ = 2 ^ k * T ^ k / ck := by
                rw [div_div_eq_mul_div]
                field_simp
        have hsum1 : ∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k
            ≤ ∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1) :=
          Finset.sum_le_sum fun k hk => hi k (Finset.mem_range.mp hk)
        have hmul1 : (2 * T / latMin Φ 1 + 1) * (∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k)
            ≤ (2 * T / latMin Φ 1 + 1) *
              (∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)) :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
        have hdist : (2 * T / latMin Φ 1 + 1) *
              (∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1))
            = ∑ k ∈ Finset.range (n + 1),
                (2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
                  + 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hQpos : gonPP Φ (k + 1) ≠ 0 := ne_of_gt (gonPP_pos Φ hΦ (by
            have := Finset.mem_range.mp hk; omega))
          have hΛne : latMin Φ 1 ≠ 0 := ne_of_gt hΛpos
          field_simp
          ring
        have hT1 : ∑ k ∈ Finset.range (n + 1), 2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
            ≤ 2 ^ (n + 1) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by
          have h_a : ∑ k ∈ Finset.range (n + 1), 2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
              ≤ ∑ k ∈ Finset.range (n + 1), 2 ^ (n + 1) * (T ^ (k + 1) / gonPP Φ (k + 1)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' : k + 1 ≤ n + 1 := by have := Finset.mem_range.mp hk; omega
            have h2 : 0 ≤ T ^ (k + 1) / gonPP Φ (k + 1) :=
              div_nonneg (by positivity) (gonPP_pos Φ hΦ (by omega)).le
            calc 2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
                = 2 ^ (k + 1) * (T ^ (k + 1) / gonPP Φ (k + 1)) := by ring
              _ ≤ 2 ^ (n + 1) * (T ^ (k + 1) / gonPP Φ (k + 1)) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk') h2
          have h_b : ∑ k ∈ Finset.range (n + 1), T ^ (k + 1) / gonPP Φ (k + 1)
              ≤ ∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s := by
            have h := Finset.sum_range_succ' (fun s => T ^ s / gonPP Φ s) (n + 1)
            have h' : ∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s
                = (∑ k ∈ Finset.range (n + 1), T ^ (k + 1) / gonPP Φ (k + 1)) + T ^ 0 / gonPP Φ 0 := by
              rw [show n + 2 = (n + 1) + 1 from rfl, h]
            rw [h']
            exact le_add_of_nonneg_right (div_nonneg (by positivity)
              (gonPP_pos Φ hΦ (Nat.zero_le _)).le)
          calc ∑ k ∈ Finset.range (n + 1), 2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
              ≤ ∑ k ∈ Finset.range (n + 1), 2 ^ (n + 1) * (T ^ (k + 1) / gonPP Φ (k + 1)) := h_a
            _ = 2 ^ (n + 1) * (∑ k ∈ Finset.range (n + 1), T ^ (k + 1) / gonPP Φ (k + 1)) := by
                rw [Finset.mul_sum]
            _ ≤ 2 ^ (n + 1) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) :=
                mul_le_mul_of_nonneg_left h_b (pow_nonneg (by norm_num) (n + 1))
        have hT2 : ∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)
            ≤ 2 ^ n * (∑ s ∈ Finset.range (n + 1), T ^ s / gonPP Φ s) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          set ck : ℝ := ∏ j ∈ Finset.range k, latMin Φ (j + 2) with hck
          have hck_pos : 0 < ck := by
            rw [hck]
            refine Finset.prod_pos fun j hj => ?_
            exact gon_latMin_pos Φ hΦ (by omega) (by have := Finset.mem_range.mp hj; omega)
          have hPk_pos : 0 < gonPP Φ k := gonPP_pos Φ hΦ (by omega)
          have hle : gonPP Φ k ≤ ck := by
            rw [hck, gonPP]
            refine Finset.prod_le_prod₀
              (fun j hj => (gon_latMin_pos Φ hΦ (by omega) (by have := Finset.mem_range.mp hj; omega)).le)
              (fun j hj => gon_latMin_mono Φ (by omega) (by have := Finset.mem_range.mp hj; omega))
          have hPP1 : gonPP Φ (k + 1) = ck * latMin Φ 1 := by rw [hck]; exact gonPP_shift Φ k
          have hgoal : 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1) = 2 ^ k * T ^ k / ck := by
            rw [hPP1]
            field_simp
          rw [hgoal]
          have step2 : 2 ^ k * T ^ k / ck ≤ 2 ^ k * T ^ k / gonPP Φ k :=
            div_le_div_of_nonneg_left (by positivity) hPk_pos hle
          have step3 : 2 ^ k * T ^ k / gonPP Φ k ≤ 2 ^ n * (T ^ k / gonPP Φ k) := by
            have h2 : 0 ≤ T ^ k / gonPP Φ k := div_nonneg (by positivity) hPk_pos.le
            calc 2 ^ k * T ^ k / gonPP Φ k = 2 ^ k * (T ^ k / gonPP Φ k) := by ring
              _ ≤ 2 ^ n * (T ^ k / gonPP Φ k) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk') h2
          exact step2.trans step3
        have hSm : (∑ s ∈ Finset.range (n + 1), T ^ s / gonPP Φ s)
            ≤ (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx
            exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
          · intro x hx _
            exact div_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ T) x)
              (gonPP_pos Φ hΦ (by have := Finset.mem_range.mp hx; omega)).le
        have hSnonneg : 0 ≤ ∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s :=
          Finset.sum_nonneg fun s hs => div_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ T) s)
            (gonPP_pos Φ hΦ (by have := Finset.mem_range.mp hs; omega)).le
        calc (2 * T / latMin Φ 1 + 1) * (∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k)
            ≤ (2 * T / latMin Φ 1 + 1) *
                (∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)) := hmul1
          _ = ∑ k ∈ Finset.range (n + 1),
                (2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1)
                  + 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)) := hdist
          _ = (∑ k ∈ Finset.range (n + 1), 2 ^ (k + 1) * T ^ (k + 1) / gonPP Φ (k + 1))
              + (∑ k ∈ Finset.range (n + 1), 2 ^ k * latMin Φ 1 * T ^ k / gonPP Φ (k + 1)) :=
              Finset.sum_add_distrib
          _ ≤ 2 ^ (n + 1) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s)
              + 2 ^ n * (∑ s ∈ Finset.range (n + 1), T ^ s / gonPP Φ s) := add_le_add hT1 hT2
          _ ≤ 2 ^ (n + 1) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s)
              + 2 ^ n * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hSm
                  (pow_nonneg (by norm_num) n))
          _ = (2 ^ (n + 1) + 2 ^ n) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by ring
          _ ≤ 2 ^ (n + 2) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by
                refine mul_le_mul_of_nonneg_right ?_ hSnonneg
                have h3 : (2:ℝ) ^ n ≤ 2 ^ (n + 1) :=
                  pow_le_pow_right₀ (by norm_num) (by omega)
                calc (2:ℝ) ^ (n + 1) + 2 ^ n ≤ (2:ℝ) ^ (n + 1) + 2 ^ (n + 1) :=
                      add_le_add le_rfl h3
                  _ = (2:ℝ) ^ (n + 2) := by ring
      calc (latCount Φ T : ℝ)
          ≤ (2 * T / latMin Φ 1 + 1) * (K * ∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k) := hstep
        _ = K * ((2 * T / latMin Φ 1 + 1) * (∑ k ∈ Finset.range (n + 1), T ^ k / gonPP Ψ k)) := by ring
        _ ≤ K * (2 ^ (n + 2) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s)) :=
            mul_le_mul_of_nonneg_left hkey hKpos.le
        _ = K * 2 ^ (n + 2) * (∑ s ∈ Finset.range (n + 2), T ^ s / gonPP Φ s) := by ring



/-! ## Helpers: power differences -/

lemma gon_pow_sub_pow_le_succ (T D : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D) (n : ℕ) :
    (T + D) ^ (n + 1) - T ^ (n + 1) ≤ ((n : ℝ) + 1) * D * (T + D) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : (T + D) ^ (m + 2) - T ^ (m + 2)
        = (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) + D * T ^ (m + 1) := by ring
    rw [h]
    have h2 : (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) ≤
        (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : D * T ^ (m + 1) ≤ D * (T + D) ^ (m + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT (by linarith) (m + 1)) hD
    have h5 : (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) + D * T ^ (m + 1) ≤
        (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) + D * (T + D) ^ (m + 1) :=
      add_le_add h2 h3
    have h6 : (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) + D * (T + D) ^ (m + 1)
        = (((m + 1 : ℕ) : ℝ) + 1) * D * (T + D) ^ (m + 1) := by push_cast; ring
    exact h5.trans (le_of_eq h6)

lemma gon_gon_pow_sub_pow_le_succ' (T D : ℝ) (hD : 0 ≤ D) (hDT : D ≤ T) (n : ℕ) :
    T ^ (n + 1) - (T - D) ^ (n + 1) ≤ ((n : ℝ) + 1) * D * T ^ n := by
  have h := gon_pow_sub_pow_le_succ (T - D) D (by linarith) hD n
  rwa [sub_add_cancel] at h






/-! ## Constant bookkeeping helpers -/

lemma gon_ballVol_nonneg (k : ℕ) : 0 ≤ ballVol k := by
  rw [ballVol]
  exact ENNReal.toReal_nonneg

lemma gon_one_le_mul {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : (1:ℝ) ≤ a * b := by
  have h := mul_le_mul ha hb (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ a)
  simpa using h

lemma gon_const1_le (Kc Cc V : ℝ) (R : ℕ) (hC : 0 < Cc) (hV : 0 ≤ V) (hKc : 0 < Kc) :
    Kc ≤ (Kc + 1) * (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by
  have h1 : (1:ℝ) ≤ V + 1 := by linarith
  have h2 : (1:ℝ) ≤ (Cc + 2) ^ (R + 2) := one_le_pow₀ (by linarith)
  have h3 : (1:ℝ) ≤ (R : ℝ) + 2 := by
    have h : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    linarith
  have h4 : (1:ℝ) ≤ (V + 1) * ((Cc + 2) ^ (R + 2) * ((R : ℝ) + 2)) :=
    gon_one_le_mul h1 (gon_one_le_mul h2 h3)
  calc Kc ≤ Kc + 1 := by linarith
    _ = (Kc + 1) * 1 := by ring
    _ ≤ (Kc + 1) * ((V + 1) * ((Cc + 2) ^ (R + 2) * ((R : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
    _ = (Kc + 1) * (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by ring

lemma gon_const2_le (Cc V : ℝ) (R : ℕ) (hC : 0 < Cc) (hV : 0 ≤ V) :
    V * (R : ℝ) * Cc * (1 + Cc) ^ (R - 1) ≤
      (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by
  have hRN : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have h1 : V * (R : ℝ) ≤ (V + 1) * ((R : ℝ) + 2) :=
    mul_le_mul (by linarith) (by linarith) hRN (by linarith)
  have hp : Cc * (1 + Cc) ^ (R - 1) ≤ (Cc + 2) ^ (R + 2) := by
    have ha : Cc * (1 + Cc) ^ (R - 1) ≤ (Cc + 2) * (Cc + 2) ^ (R - 1) :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) _)
        (by positivity) (by linarith)
    have hb : (Cc + 2) * (Cc + 2) ^ (R - 1) = (Cc + 2) ^ ((R - 1) + 1) :=
      (pow_succ' (Cc + 2) (R - 1)).symm
    rw [hb] at ha
    exact le_trans ha (pow_le_pow_right₀ (by linarith) (by omega))
  calc V * (R : ℝ) * Cc * (1 + Cc) ^ (R - 1)
      = (V * (R : ℝ)) * (Cc * (1 + Cc) ^ (R - 1)) := by ring
    _ ≤ ((V + 1) * ((R : ℝ) + 2)) * (Cc + 2) ^ (R + 2) :=
        mul_le_mul h1 hp (by positivity) (by positivity)
    _ = (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by ring

lemma gon_const3_le (Cc V : ℝ) (R : ℕ) (hC : 0 < Cc) (hV : 0 ≤ V) :
    V * Cc ≤ (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by
  have h4 : Cc ≤ (Cc + 2) := by linarith
  have h5 : (Cc + 2) ≤ (Cc + 2) ^ (R + 2) := by
    calc (Cc + 2) = (Cc + 2) ^ 1 := by ring
      _ ≤ (Cc + 2) ^ (R + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  have h6 : (Cc + 2) ^ (R + 2) ≤ (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) :=
    le_mul_of_one_le_right (by positivity) (by
      have h : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith)
  have h3 : Cc ≤ (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := le_trans h4 (le_trans h5 h6)
  calc V * Cc ≤ (V + 1) * ((Cc + 2) ^ (R + 2) * ((R : ℝ) + 2)) :=
        mul_le_mul (by linarith) h3 (by linarith) (by linarith)
    _ = (V + 1) * (Cc + 2) ^ (R + 2) * ((R : ℝ) + 2) := by ring

lemma gon_target_rhs (T Y cov : ℝ) (hT : T ≠ 0) {R : ℕ} (hR : 1 ≤ R) :
    T ^ R / cov * (Y / T) = Y * T ^ (R - 1) / cov := by
  have h1 : T ^ R = T ^ (R - 1) * T := by rw [← pow_succ]; congr 1; omega
  rw [h1, div_mul_div_comm]
  rw [show T ^ (R - 1) * T * Y = (T ^ (R - 1) * Y) * T by ring]
  rw [mul_div_mul_right _ _ hT]
  ring



/-- N03. Geometry of numbers: the Schmidt/Davenport upper bound and the asymptotic ball count
with error `Y/T` for `Y ≥ λ_R`. -/
theorem gon (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T Y : ℝ), 1 ≤ rk L → 1 ≤ T →
      ((ballCount L T : ℝ) ≤ K * ∑ i ∈ Finset.range (rk L + 1),
          T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1)) ∧
      (lam L (rk L) ≤ Y → Y ≤ T →
        |(ballCount L T : ℝ) - ballVol (rk L) * T ^ rk L / detL L|
          ≤ K * T ^ rk L / detL L * (Y / T)) := by
  classical
  choose Kc hKc using fun R : ℕ => gon_latCount_upper (ι := ι) R
  choose Cc hCc using fun R : ℕ => exists_short_basis (ι := ι) R
  set Ksum : ℝ := ∑ R ∈ Finset.range (Fintype.card ι + 1),
      (Kc R + 1) * (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2) with hKsum
  have htermpos : ∀ R' : ℕ, 0 < (Kc R' + 1) * (ballVol R' + 1) * (Cc R' + 2) ^ (R' + 2)
      * ((R' : ℝ) + 2) := by
    intro R'
    have h1 : (0:ℝ) < Kc R' + 1 := by linarith [(hKc R').1]
    have h2 : (0:ℝ) < ballVol R' + 1 := by linarith [gon_ballVol_nonneg R']
    have h3 : (0:ℝ) < Cc R' + 2 := by linarith [(hCc R').1]
    have h4 : (0:ℝ) < (Cc R' + 2) ^ (R' + 2) := pow_pos h3 _
    have h5 : (0:ℝ) < (R' : ℝ) + 2 := by
      have hh : (0:ℝ) ≤ (R' : ℝ) := Nat.cast_nonneg R'
      linarith
    exact mul_pos (mul_pos (mul_pos h1 h2) h4) h5
  have hfnn : ∀ R' ∈ Finset.range (Fintype.card ι + 1),
      0 ≤ (Kc R' + 1) * (ballVol R' + 1) * (Cc R' + 2) ^ (R' + 2) * ((R' : ℝ) + 2) :=
    fun R' _ => (htermpos R').le
  have hKpos : 0 < Ksum := by
    rw [hKsum]
    exact Finset.sum_pos (fun R' _ => htermpos R')
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  refine ⟨Ksum, hKpos, ?_⟩
  intro L T Y hRk hT
  set e := Submodule.basisOfPid (Pi.basisFun ℤ ι) L with he
  obtain ⟨R, b⟩ := e
  have he' : Submodule.basisOfPid (Pi.basisFun ℤ ι) L = ⟨R, b⟩ := he.symm
  have hrank : rk L = R := by
    have h1 : rk L = Module.finrank ℤ L := rfl
    rw [h1, Module.finrank_eq_card_basis b]
    simp
  have hR : 1 ≤ R := by rw [← hrank]; exact hRk
  have hRle : R ≤ Fintype.card ι := by
    have h1 : R = Module.finrank ℤ L := by rw [← hrank]; rfl
    rw [h1]
    calc Module.finrank ℤ L ≤ Module.finrank ℤ (ι → ℤ) := Submodule.finrank_le L
      _ = Fintype.card ι := (Module.finrank_fintype_fun_eq_card ℤ : _)
  have hmem : R ∈ Finset.range (Fintype.card ι + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hRle)
  have hfR : (Kc R + 1) * (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2) ≤ Ksum := by
    rw [hKsum]
    exact Finset.single_le_sum hfnn hmem
  have hfR' : (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2) ≤ Ksum := by
    refine le_trans ?_ hfR
    have h1 : (1:ℝ) ≤ Kc R + 1 := by linarith [(hKc R).1]
    have h2 : 0 ≤ (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2) :=
      mul_nonneg (mul_nonneg (by linarith [gon_ballVol_nonneg R])
        (pow_nonneg (by linarith [(hCc R).1]) _))
        (by have h : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R; linarith)
    calc (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2)
        = 1 * ((ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2)) := by ring
      _ ≤ (Kc R + 1) * ((ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (Kc R + 1) * (ballVol R + 1) * (Cc R + 2) ^ (R + 2) * ((R : ℝ) + 2) := by ring
  have hKc_le : Kc R ≤ Ksum :=
    le_trans (gon_const1_le (Kc R) (Cc R) (ballVol R) R (hCc R).1 (gon_ballVol_nonneg R) (hKc R).1) hfR
  have hVRC : ballVol R * (R : ℝ) * Cc R * (1 + Cc R) ^ (R - 1) ≤ Ksum :=
    le_trans (gon_const2_le (Cc R) (ballVol R) R (hCc R).1 (gon_ballVol_nonneg R)) hfR'
  have hVC : ballVol R * Cc R ≤ Ksum :=
    le_trans (gon_const3_le (Cc R) (ballVol R) R (hCc R).1 (gon_ballVol_nonneg R)) hfR'
  set Φ : LatMap (ι := ι) R := phiOf (vb b) with hΦdef
  have hv : LinearIndependent ℤ (vb b) :=
    LinearIndependent.map' b.linearIndependent (Submodule.subtype L) (Submodule.ker_subtype L)
  have hΦ : Function.Injective Φ := by
    rw [hΦdef]; exact phiOf_injective (vb b) hv
  have hbC : ballCount L T = latCount Φ T := by
    rw [hΦdef]; exact ballCount_eq_latCount b T
  have hbL : lam L R = latMin Φ R := by rw [hΦdef]; exact lam_eq_latMin b R
  have hprod : ∀ k, (∏ j ∈ Finset.range k, lam L (j + 1)) = gonPP Φ k := fun k => by
    rw [gonPP]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hΦdef]; exact lam_eq_latMin b (j + 1)
  have hbD : detL L = latCovol Φ := by
    rw [hΦdef]
    unfold detL latCovol
    rw [he']
    refine congrArg Real.sqrt (congrArg Matrix.det ?_)
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply]
    simp only [Pi.basisFun_apply, phiOf_single, gon_inner_toLp, vb]
  refine ⟨?_, ?_⟩
  · rw [hrank]
    have hsum : ∑ i ∈ Finset.range (R + 1),
          T ^ (R - i) / ∏ j ∈ Finset.range (R - i), lam L (j + 1)
        = ∑ k ∈ Finset.range (R + 1), T ^ k / gonPP Φ k := by
      simp only [hprod]
      simpa using Finset.sum_range_reflect (fun k => T ^ k / gonPP Φ k) (R + 1)
    rw [hbC, hsum]
    have h1 := (hKc R).2 Φ hΦ T hT
    have h2 : 0 ≤ ∑ k ∈ Finset.range (R + 1), T ^ k / gonPP Φ k :=
      Finset.sum_nonneg fun k hk =>
        div_nonneg (by positivity) (gonPP_pos Φ hΦ (by have := Finset.mem_range.mp hk; omega)).le
    calc (latCount Φ T : ℝ) ≤ Kc R * (∑ k ∈ Finset.range (R + 1), T ^ k / gonPP Φ k) := h1
      _ ≤ Ksum * (∑ k ∈ Finset.range (R + 1), T ^ k / gonPP Φ k) :=
          mul_le_mul_of_nonneg_right hKc_le h2
  · rw [hrank, hbC, hbD, hbL]
    intro hYR hYT
    obtain ⟨e2, he2⟩ := (hCc R).2 Φ hΦ
    set C : ℝ := Cc R with hCdef
    set D : ℝ := ∑ i, ‖Φ (fun k => ((e2 i) k : ℝ))‖ with hDdef
    have hCpos : 0 < C := by rw [hCdef]; exact (hCc R).1
    have hDnn : 0 ≤ D := by
      rw [hDdef]; exact Finset.sum_nonneg fun i _ => norm_nonneg _
    have hDleCY : D ≤ C * Y := by
      rw [hDdef, hCdef]
      exact le_trans he2 (mul_le_mul_of_nonneg_left hYR (hCc R).1.le)
    have hcube := gon_cube hR Φ hΦ e2
    have hTpos : 0 < T := by linarith
    have hTne : T ≠ 0 := ne_of_gt hTpos
    have hYpos : 0 < Y := lt_of_lt_of_le (gon_latMin_pos Φ hΦ hR le_rfl) hYR
    have hYnn : 0 ≤ Y := hYpos.le
    have hcovnn : 0 ≤ latCovol Φ := Real.sqrt_nonneg _
    have hVnn : 0 ≤ ballVol R := gon_ballVol_nonneg R
    have hTnn : 0 ≤ T := hTpos.le
    have hT0 : (0:ℝ) ≤ T ^ (R - 1) := pow_nonneg hTnn _
    have hTR : T ^ R = T ^ (R - 1) * T := by rw [← pow_succ]; congr 1; omega
    have hR1 : R - 1 + 1 = R := Nat.succ_pred_eq_of_pos hR
    have hcast : ((R - 1 : ℕ) : ℝ) + 1 = (R : ℝ) := by
      have h2 : ((R - 1 : ℕ) : ℝ) + 1 = ((R - 1 + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [h2, hR1]
    have hDleCT : D ≤ C * T :=
      le_trans hDleCY (mul_le_mul_of_nonneg_left hYT hCpos.le)
    have hexp : (T + D) ^ (R - 1) ≤ (1 + C) ^ (R - 1) * T ^ (R - 1) := by
      have hTD : T + D ≤ (1 + C) * T := by nlinarith [hDleCT]
      calc (T + D) ^ (R - 1) ≤ ((1 + C) * T) ^ (R - 1) := pow_le_pow_left₀ (by linarith) hTD _
        _ = (1 + C) ^ (R - 1) * T ^ (R - 1) := by rw [mul_pow]
    have hrhs : Ksum * T ^ R / latCovol Φ * (Y / T) = Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by
      calc Ksum * T ^ R / latCovol Φ * (Y / T)
          = Ksum * (T ^ R / latCovol Φ * (Y / T)) := by ring
        _ = Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by
            rw [gon_target_rhs T Y (latCovol Φ) hTne hR]
    have hVRC' : ballVol R * (R : ℝ) * C ≤ Ksum := by
      have h1 : (1:ℝ) ≤ (1 + C) ^ (R - 1) := one_le_pow₀ (by linarith)
      have h2 : 0 ≤ ballVol R * (R : ℝ) * C :=
        mul_nonneg (mul_nonneg hVnn (Nat.cast_nonneg R)) hCpos.le
      have h3 : ballVol R * (R : ℝ) * C * 1 ≤ ballVol R * (R : ℝ) * C * (1 + C) ^ (R - 1) :=
        mul_le_mul_of_nonneg_left h1 h2
      calc ballVol R * (R : ℝ) * C = ballVol R * (R : ℝ) * C * 1 := by ring
        _ ≤ ballVol R * (R : ℝ) * C * (1 + C) ^ (R - 1) := h3
        _ ≤ Ksum := hVRC
    have hupper : (latCount Φ T : ℝ) - ballVol R * T ^ R / latCovol Φ ≤
        Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by
      have h1 : (latCount Φ T : ℝ) ≤ ballVol R * (T + D) ^ R / latCovol Φ := hcube.1 T hTnn
      have h2 : (T + D) ^ R - T ^ R ≤ (R : ℝ) * D * (T + D) ^ (R - 1) := by
        have h := gon_pow_sub_pow_le_succ T D hTnn hDnn (R - 1)
        rw [hcast, hR1] at h
        exact h
      have h3 : D * (T + D) ^ (R - 1) ≤ C * Y * ((1 + C) ^ (R - 1) * T ^ (R - 1)) :=
        mul_le_mul hDleCY hexp (pow_nonneg (by linarith) _)
          (mul_nonneg hCpos.le hYnn)
      calc (latCount Φ T : ℝ) - ballVol R * T ^ R / latCovol Φ
          ≤ ballVol R * (T + D) ^ R / latCovol Φ - ballVol R * T ^ R / latCovol Φ := by
            linarith
        _ = ballVol R * ((T + D) ^ R - T ^ R) / latCovol Φ := by ring
        _ ≤ ballVol R * (R : ℝ) * D * (T + D) ^ (R - 1) / latCovol Φ := by
            apply div_le_div_of_nonneg_right _ hcovnn
            calc ballVol R * ((T + D) ^ R - T ^ R)
                ≤ ballVol R * ((R : ℝ) * D * (T + D) ^ (R - 1)) :=
                  mul_le_mul_of_nonneg_left h2 hVnn
              _ = ballVol R * (R : ℝ) * D * (T + D) ^ (R - 1) := by ring
        _ ≤ ballVol R * (R : ℝ) * C * Y * ((1 + C) ^ (R - 1) * T ^ (R - 1)) / latCovol Φ := by
            apply div_le_div_of_nonneg_right _ hcovnn
            calc ballVol R * (R : ℝ) * D * (T + D) ^ (R - 1)
                = ballVol R * (R : ℝ) * (D * (T + D) ^ (R - 1)) := by ring
              _ ≤ ballVol R * (R : ℝ) * (C * Y * ((1 + C) ^ (R - 1) * T ^ (R - 1))) :=
                  mul_le_mul_of_nonneg_left h3 (by positivity)
              _ = ballVol R * (R : ℝ) * C * Y * ((1 + C) ^ (R - 1) * T ^ (R - 1)) := by ring
        _ ≤ Ksum * (Y * T ^ (R - 1)) / latCovol Φ := by
            apply div_le_div_of_nonneg_right _ hcovnn
            calc ballVol R * (R : ℝ) * C * Y * ((1 + C) ^ (R - 1) * T ^ (R - 1))
                = (ballVol R * (R : ℝ) * C * (1 + C) ^ (R - 1)) * (Y * T ^ (R - 1)) := by ring
              _ ≤ Ksum * (Y * T ^ (R - 1)) :=
                  mul_le_mul_of_nonneg_right hVRC (mul_nonneg hYnn hT0)
        _ = Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by ring
    have hlower : -(Ksum * (Y * T ^ (R - 1) / latCovol Φ)) ≤
        (latCount Φ T : ℝ) - ballVol R * T ^ R / latCovol Φ := by
      have hgoal : ballVol R * T ^ R / latCovol Φ - (latCount Φ T : ℝ) ≤
          Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by
        by_cases hDT : D ≤ T
        · have h1 : ballVol R * (T - D) ^ R / latCovol Φ ≤ (latCount Φ T : ℝ) := hcube.2 T hDT
          have h2 : T ^ R - (T - D) ^ R ≤ (R : ℝ) * D * T ^ (R - 1) := by
            have h := gon_gon_pow_sub_pow_le_succ' T D hDnn hDT (R - 1)
            rw [hcast, hR1] at h
            exact h
          have h3 : D * T ^ (R - 1) ≤ C * Y * T ^ (R - 1) :=
            mul_le_mul_of_nonneg_right hDleCY hT0
          calc ballVol R * T ^ R / latCovol Φ - (latCount Φ T : ℝ)
              ≤ ballVol R * T ^ R / latCovol Φ - ballVol R * (T - D) ^ R / latCovol Φ := by
                linarith
            _ = ballVol R * (T ^ R - (T - D) ^ R) / latCovol Φ := by ring
            _ ≤ ballVol R * (R : ℝ) * D * T ^ (R - 1) / latCovol Φ := by
                apply div_le_div_of_nonneg_right _ hcovnn
                calc ballVol R * (T ^ R - (T - D) ^ R)
                    ≤ ballVol R * ((R : ℝ) * D * T ^ (R - 1)) :=
                      mul_le_mul_of_nonneg_left h2 hVnn
                  _ = ballVol R * (R : ℝ) * D * T ^ (R - 1) := by ring
            _ ≤ ballVol R * (R : ℝ) * C * Y * T ^ (R - 1) / latCovol Φ := by
                apply div_le_div_of_nonneg_right _ hcovnn
                calc ballVol R * (R : ℝ) * D * T ^ (R - 1)
                    = ballVol R * (R : ℝ) * (D * T ^ (R - 1)) := by ring
                  _ ≤ ballVol R * (R : ℝ) * (C * Y * T ^ (R - 1)) :=
                      mul_le_mul_of_nonneg_left h3 (by positivity)
                  _ = ballVol R * (R : ℝ) * C * Y * T ^ (R - 1) := by ring
            _ ≤ Ksum * (Y * T ^ (R - 1)) / latCovol Φ := by
                apply div_le_div_of_nonneg_right _ hcovnn
                calc ballVol R * (R : ℝ) * C * Y * T ^ (R - 1)
                    = (ballVol R * (R : ℝ) * C) * (Y * T ^ (R - 1)) := by ring
                  _ ≤ Ksum * (Y * T ^ (R - 1)) :=
                      mul_le_mul_of_nonneg_right hVRC' (mul_nonneg hYnn hT0)
            _ = Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by ring
        · push_neg at hDT
          have hCY : T < C * Y := lt_of_lt_of_le hDT hDleCY
          have hVT : ballVol R * T ≤ Ksum * Y := by
            calc ballVol R * T ≤ ballVol R * (C * Y) := mul_le_mul_of_nonneg_left hCY.le hVnn
              _ = ballVol R * C * Y := by ring
              _ ≤ Ksum * Y := mul_le_mul_of_nonneg_right hVC hYnn
          have h2 : (0:ℝ) ≤ (latCount Φ T : ℝ) := Nat.cast_nonneg _
          calc ballVol R * T ^ R / latCovol Φ - (latCount Φ T : ℝ)
              ≤ ballVol R * T ^ R / latCovol Φ := by linarith
            _ = (ballVol R * T) * (T ^ (R - 1) / latCovol Φ) := by
                rw [hTR]; ring
            _ ≤ (Ksum * Y) * (T ^ (R - 1) / latCovol Φ) :=
                mul_le_mul_of_nonneg_right hVT (by positivity)
            _ = Ksum * (Y * T ^ (R - 1) / latCovol Φ) := by ring
      linarith
    have habs : |(latCount Φ T : ℝ) - ballVol R * T ^ R / latCovol Φ| ≤
        Ksum * (Y * T ^ (R - 1) / latCovol Φ) := abs_le.mpr ⟨hlower, hupper⟩
    rw [hrhs]
    exact habs

end Work.HP
